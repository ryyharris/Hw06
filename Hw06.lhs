You are free to write whatever error messages you like, though please be sure (a) that they go to stderr (not stdout) and (b) that you exit with a non-zero exit code.

Do not output unnecessary text when a program succeeds.
1 Implement the parser and the -c checking-mode flag. Leave the interpreter stubbed out, but write tests for the parser and the checker. Write the command-line interface/argument parser.
2 Implement the interpreter. Write tests for the interpreter. Extend the argument parser.
3 Implement the -n Church-numeral conversion flag. Write tests for the Church-numeral conversion and extend the argument parser.


> {-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing -fno-warn-incomplete-patterns -fno-warn-missing-signatures -fno-warn-unused-imports #-}

> module Hw06 where
> import Control.Applicative
> import Control.Exception
> import Data.Char
> import Test.QuickCheck
> import System.Random
> import System.Environment
> import System.IO  
> import System.IO.Error
> import System.Exit
> import Data.Either
> import Data.Maybe



> -- GRAMMAR ->   e ::= x | e1 e2 | lambda x. e

> type VarName = String

> data LambdaCalc =
>     Var VarName
>   | Apply LambdaCalc LambdaCalc -- Seq (Var "x") (Var "y") == x y
>   | Lambda [VarName] LambdaCalc -- Lam (Var "x" , Var "y") (Var "z") == lam x y . z
>   | Assign VarName LambdaCalc LambdaCalc
>   | Paren LambdaCalc
>	deriving (Show, Eq)


> data Token =
>     TLet
>   | TIn
>   | TLambda 
>   | TLParen
>   | TRParen
>   | TDot
>   | TEq
>   | TVar String -- x or e from lambda x. e
>   deriving (Show, Eq)

> lexer :: String -> [Token]
> lexer []                      = []
> lexer (w:s) | isSpace w       = lexer (dropWhile isSpace s)
> lexer ('(':s)      		= TLParen:lexer s
> lexer (')':s)      		= TRParen:lexer s
> lexer ('l':'e':'t':' ':s)     = TLet:lexer s
> lexer ('i':'n':' ':s)         = TIn:lexer s
> lexer ('.':s)                 = TDot:lexer s
> lexer ('l':'a':'m':'b':'d':'a':' ':s)  = TLambda:lexer s
> lexer ('=':s)                 = TEq:lexer s
> lexer s | isAlpha (head s) =
>   let (var,s') =  span (\char -> isAlphaNum char || char == (head "'")) s in 
>   TVar var:lexer s'
> lexer (n:_) = error $ "Lexer error: unexpected character " ++ [n]


> newtype Parser a = Parser { parse :: String -> Maybe (a,String) }

> instance Functor Parser where
>   fmap f p = Parser $ \s -> (\(a,c) -> (f a, c)) <$> parse p s

> instance Applicative Parser where
>   pure a = Parser $ \s -> Just (a,s)
>   f <*> a = Parser $ \s ->
>     case parse f s of
>       Just (g,s') -> parse (fmap g a) s'
>       Nothing -> Nothing

> instance Alternative Parser where
>   empty = Parser $ \s -> Nothing
>   l <|> r = Parser $ \s -> parse l s <|> parse r s

> ensure :: (a -> Bool) -> Parser a -> Parser a
> ensure p parser = Parser $ \s ->
>    case parse parser s of
>      Nothing -> Nothing
>      Just (a,s') -> if p a then Just (a,s') else Nothing
>
> lookahead :: Parser (Maybe Char)
> lookahead = Parser f
>   where f [] = Just (Nothing,[])
>         f (c:s) = Just (Just c,c:s)
>
> satisfy :: (Char -> Bool) -> Parser Char
> satisfy p = Parser f
>   where f [] = Nothing
>         f (x:xs) = if p x then Just (x,xs) else Nothing

> int :: Parser Int
> int = read <$> some (satisfy isDigit)

> eof :: Parser ()
> eof = Parser $ \s -> if null s then Just ((),[]) else Nothing
> ws :: Parser ()
> ws = pure () <* many (satisfy isSpace)
>
> char :: Char -> Parser Char
> char c = ws *> satisfy (==c)
>
> str :: String -> Parser String
> str s = ws *> loop s
>   where loop [] = pure []
>         loop (c:cs) = (:) <$> satisfy (==c) <*> loop cs

> parens :: Parser a -> Parser a
> parens p = (char '(' *> p) <* char ')'

> keywords :: [String]
> keywords = ["let", "in", "lambda"]
>
> isKeyword = (`elem` keywords)
> kw :: String -> Parser String
> kw key = (str key) <* (ensure isKey lookahead) where
>                       isKey Nothing = True
>                       isKey (Just a) = not (isAlphaNum a)

> var :: Parser String
> var = ensure (not . (`elem` keywords)) (ws *> id)
>   where id = (:) <$> satisfy isAlpha <*> many (satisfy isAlphaNumSingleQuote)

> sepBy1 :: Parser a -> Parser sep -> Parser [a]
> sepBy1 p sep = (:) <$> p <*> (many (sep *> p))

> chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
> chainl1 p sep = foldl (\acc (op,v) -> op acc v) <$> 
>                 p <*> many ((\op v -> (op,v)) <$> sep <*> p)
>
> isAlphaNumSingleQuote :: Char -> Bool
> isAlphaNumSingleQuote c = isAlphaNum c || c == '\''
>
> parseVarNames = var `sepBy1` ws


> ---------------- PARSER  -----------------
>
> applyexps, assign, lexp, atom :: Parser LambdaCalc
> assign = Assign <$> (ws *> kw "let" *> var <* char '=') <*> lexp <* kw "in" <*> assign
>          <|> lexp
> lexp = Lambda <$> (ws *> kw "lambda" *> ws *> parseVarNames <* ws <* char '.') <*> lexp
>        <|> applyexps
> applyexps = atom `chainl1` (ws *> pure Apply)
> atom = Var <$> var
>        <|> (char '(' *> (Paren <$> lexp) <* char ')')


> parseApply = parse assign

> ---------------- EVALUATER  -----------------

> getList :: [String] -> LambdaCalc -> [String]
> getList lst (Var v) = lst
> getList lst (Apply x y) = (getList lst x) ++ (getList lst y)
> getList lst (Lambda x y) = getList (lst ++ x) y
> getList lst (Assign var exp1 exp2) = getList lst exp2
> getList lst (Paren exp) = getList lst exp

> isScoped :: [String] -> LambdaCalc -> Bool
> isScoped lst (Var v) = elem v lst
> isScoped lst (Apply x y) = (isScoped lst x) && (isScoped lst y)
> isScoped lst (Lambda x y) = isScoped (lst ++ x) y
> isScoped lst (Assign var exp1 exp2) = (isScoped lst exp1) && (isScoped (var:lst) exp2)
> isScoped lst (Paren exp) = isScoped lst exp


> getLC :: String -> LambdaCalc
> getLC str =  fst $ fromJust (parseApply str)

> -- Assign v l1 l2, replace any v that occur in lc2 with lc1
> beta :: LambdaCalc -> LambdaCalc
> beta (Assign var lc1 lc2) = case lc2 of
>  (Var v) -> if var == v then lc1 else lc2
>  (Apply e1 e2) -> Apply (beta (Assign var lc1 e1)) (beta (Assign var lc1 e2))
>  (Lambda vlst e) ->  Lambda vlst (beta (Assign var lc1 e))
>  (Assign v e1 e2) -> beta (Assign v e1 (beta (Assign var lc1 e2)))
>  (Paren e) -> Paren $ beta (Assign var lc1 e)
> beta x = x


> eval' :: LambdaCalc -> Either String LambdaCalc
> eval' (Var v) = Right $ Var v
> eval' (Lambda vlst e) = Right (Lambda vlst e)
> eval' (Paren e) = case eval' e of
>   Left e -> Left e
>   Right lc -> Right $ Paren lc
> eval' (Apply e1 e2) =  case removeParen $ eval' e1 of
>   Left e -> Left e
>   Right (Lambda (v:vs) e1') -> case removeParen $ eval' e2 of
>     Left e' -> Left e'
>     Right e2' ->  if null vs
>                   then eval' (beta (Assign v e2' e1'))
>                   else  eval' $ Lambda vs (beta (Assign v e2' e1'))
>   otherwise -> Left $ "e1 invalid "++ show e1 ++ "\n"
> 
> subst' :: LambdaCalc -> VarName -> LambdaCalc -> LambdaCalc
> subst' (Var v) var e2          = if v == var then e2
>                                else Var v
> subst' (Apply lam1 lam2) x e2  = Apply (subst' lam1 x e2) (subst' lam2 x e2)
> subst' (Paren e1) x e2         = subst' e1 x e1
> subst' (Lambda [] e1) x e2 = subst' e1 x e2 
> subst' (Lambda (v:vs) e1) x e2 = substHelp (Assign x (Lambda (v:vs) e1) e2 )
> substHelp (Assign var lc1 lc2) = case lc2 of
>    (Var v) -> if var == v then lc1 else lc2
>    (Apply e1 e2) -> Apply (substHelp (Assign var lc1 e1)) (substHelp (Assign var lc1 e2))
>    (Lambda vlst e) ->  if var `elem` vlst
>                        then (Lambda vlst e)
>                        else Lambda vlst (substHelp (Assign var lc1 e))
>    (Assign v e1 e2) -> substHelp (Assign v e1 (substHelp (Assign var lc1 e2)))
>    (Paren e) -> Paren $ substHelp (Assign var lc1 e)
> substHelp e = e

> removeParen (Right (Paren e)) = removeParen $ Right e
> removeParen (Right e) = Right e
> removeParen (Left e) = Left e



> ---------------- PRINTER  -----------------

> printer ::  Either String LambdaCalc -> IO String
> printer (Left error) = die error
> printer (Right lc) = return $ prettyPrint lc  

> prettyPrint :: LambdaCalc -> String
> prettyPrint (Var v) = v
> prettyPrint (Paren e) = "(" ++ prettyPrint e ++ ")"
> prettyPrint (Lambda vs e) = "lambda " ++ unwords vs ++ ". " ++ prettyPrint e
> prettyPrint (Apply e1 e2) = prettyPrint e1 ++ " "++ prettyPrint e2

> printChurch :: Either String LambdaCalc -> IO String
> printChurch (Left error) = die error
> printChurch (Right lc) = case churchNum lc  of
>  Left errorMessage -> die errorMessage
>  Right value -> return $ show value

> -- lam has been completely evaluated
> churchNum :: LambdaCalc -> Either String Int
> churchNum lam = church lam 0
>   where church :: LambdaCalc -> Int -> Either String Int
>         church (Lambda (s:z:[]) e) val
>              | e == (Var z) =  Right val
>              | e == (Var s) = Left $ "Wrong value, "++s++", should be "++z
>              | otherwise = church e val
>         church (Lambda sx e) val = Left $ "Too many or few values in lambda, "++ unwords sx
>         church (Paren e) val = church e val
>         church (Apply e1 e2) val = case e1 of
>           Var s -> church e2 (val+1)
>           otherwise -> church e1 val

> result, churchResult :: String -> IO String
> result str = (printer $ eval' $ beta $ getLC str)
> churchResult str = printChurch $ eval' $ beta $ getLC str



> ---------------- MAIN/COMMAND LINE -----------------

> zero = "lambda s z. z"
> one = "lambda s z. s (lambda s z. z) s z"
> two = "lambda s z. s ((lambda s z. s ((lambda s z. z) s z)) s z)"
> three = "lambda s z. s ((lambda s z. s ((lambda s z. s ((lambda s z. z) s z)) s z)) s z)"
> three' = "let zero = lambda s z. z in let succ = lambda n. lambda s z. s (n s z) in succ (succ (succ zero))"
> four = "let zero = lambda s z. z in let succ = lambda n. lambda s z. s (n s z) in succ (succ (succ (succ zero)))"

> --finds which argument in user input is file
> findFile :: [String] -> String
> findFile [] = []
> findFile (i:is) = if (file i == True) then i
>						else findFile is

> -- Tell if a string is the cflag, nflag, a dash, or a valid file
> cflag, file, nflag, dash, cnflag :: String -> Bool
> cflag s = "-c" == s
> nflag s = "-n" == s
> file s = not (dash s || cflag s || cnflag s || nflag s)
> dash s = "-" == s
> cnflag s = "-cn" == s || "-nc" == s

> data Arguments =
>        CFlag      -- gave -c
>      | NFlag      -- gave -n
>      | CNFlag     -- gave -cn or -nc
>      | Command        -- gave - or no file name, read from command line
>      | File
>	deriving (Show, Eq)

> -- Convert list of string from command line and turn into list of Arguments
> filterCmd :: [String] -> [Arguments]
> filterCmd [] = []
> filterCmd (s:sx)
>   | file s  = File    : (filterCmd sx)
>   | nflag s = NFlag   : (filterCmd sx)
>   | dash s  = Command : (filterCmd sx)
>   | cnflag s = CNFlag : (filterCmd sx)
>   | cflag s = CFlag   : (filterCmd sx)
>   | otherwise = Command : (filterCmd sx)




> -- Does flags if they exist and then perform evaluation
> doConfig :: [Arguments] -> String -> IO String
> doConfig [] lambda = result lambda 
> doConfig (a:as) lambda 
>   | a == CFlag = if doCFlag lambda 
>                  then doConfig as lambda
>                  else return $ "The program " ++ lambda ++ " is not well scoped \n"
>   | a == Command = doConfig as lambda
>   | a == File = doConfig as lambda
>   | a == NFlag = doNConfig as lambda 
>   | a == CNFlag = if doCFlag lambda 
>                  then doNConfig as lambda
>                  else return $ "The program " ++ lambda ++ " is not well scoped \n"

> doNConfig ::  [Arguments] -> String -> IO String
> doNConfig [] lambda = churchResult lambda
> doNConfig (a:as) lambda
>   | a == CFlag = if doCFlag lambda 
>                  then doNConfig as lambda
>                  else return $ "The program \n" ++ lambda ++ "\n is not well scoped \n"
>   | a == Command = doNConfig as lambda
>   | a == File = doNConfig as lambda
>   | a == NFlag = doNConfig as lambda
>   | a == CNFlag = if doCFlag lambda 
>                  then doNConfig as lambda
>                  else return $ "The program " ++ lambda ++ " is not well scoped \n"

> doCFlag :: String -> Bool
> doCFlag str
>	| (isJust (parseApply str)) && (isScoped [] (getLC str)) = True
>	| otherwise = False

> main = main' `catch` handler

              
> toTry :: IO ()  
> toTry = do (fileName:_) <- getArgs  
>            contents <- readFile fileName  
>            putStrLn $ "The file has " ++
>                     show (length (lines contents)) ++ " lines!"  

> main' :: IO ()
> main' = do
>	 cmdArgs <- getArgs 
>        let args = filterCmd cmdArgs in
>  	   if File `elem` args then
>  	      do
>  	        lambdas <- readFile (findFile cmdArgs)
>               ans <- doConfig args lambdas
>  	        putStr $ ans ++ "\n"
>  	   else 
>  	     do
>  	       lambdas <- getLine
>              ans <- doConfig args lambdas
>              if doCFlag ans then putStr $ ans ++ "\n"
>              else die $ "error, " ++ans

> checkCorrect :: String -> String
> checkCorrect str = if doCFlag str then str else "error"

> handler :: IOError -> IO ()  
> handler e = putStrLn "Whoops, had some trouble!"  

> ---------------- TESTS  -----------------

> true' = "lambda a. lambda b . a"
> false' = "lambda a. lambda b . b"
> t1 = "(lambda x. lambda x. x) (lambda s. lambda z. s z)"

> test1 = "lambda x. x (x x)"
> test2 = "lambda x. x x x"
> test4 = "let zero = lambda s z. z in let succ = lambda n. lambda s z. s (n s z) in succ (succ (succ zero))"
> test5 = "lambda s z. s z"  --  should parse like test6
> test6 = "lambda s. (lambda z. (s z))"
> testlet1 = "let x = y in lambda y . y" -- lambda y . y , fails on -c
> testlet3 = "let id = lambda x. x in lambda y. id" --lambda y. lambda x. x
> testlet4 = "let id = lambda x.x in let da = lambda s. (s s) in id da" --lambda s. (s s)

> -- SHOULD BE INVALID
> test3 = "let x = e1 in e2"
> test7 = "lambda foo3'5bar. x "
> test8 = "x y z"   -- Should parse like test9
> test9 = "(x y) z"
> testlet2 = "let x = y in lambda t . y"
> test10 = "'quoted'"
> test11 = "12"


