# Daniel Jin
# Rae Harris
#

interp : Hw06.lhs 
	stack ghc -- -main-is Hw06.main -o $@ $^

test : interp tests/*
	for t in tests/*; do ./interp $$t; done

clean :
	rm interp
	rm *.hi *.o

.PHONY: test clean

Hw06.zip: *.lhs *.md *.lc Makefile
	rm -f Hw06.zip && zip Hw06 *.lhs *.md *.lc Makefile
