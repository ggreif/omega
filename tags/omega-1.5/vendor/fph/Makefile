GHC=ghc -Wall -fglasgow-exts
LATEX=latex
DVISPS=dvips

FILES=`ls *lhs` 

all:
	$(GHC) --make $(FILES)


clean:
	$(RM) *.hi *.o *~ .*swp a.out *.exe
