MAIN             = Main
EXT              = .exe
EXEC             = omega$(EXT)
GHC              = ghc
GHCI             = ghci
GHC_FLAGS        = -auto-all $(GHC_OPT_FLAGS) $(GHC_FLAGS_COMMON)
GHCI_FLAGS       = $(GHC_FLAGS_COMMON)
GHC_FLAGS_COMMON = -fglasgow-exts -XUndecidableInstances
GHC_OPT_FLAGS    = 
HUGS             = hugs
HUGS_FLAGS       = -98 -P:../Lib:../Lib/Parser
SVN              = svn

.PHONY: all tests clean manual update

all: *.hs
	$(GHC) $(GHC_FLAGS) -o $(EXEC) --make $(MAIN)

%: %.hs *.hs
	$(GHC) $(GHC_FLAGS) --make $*

ghci-%: %.hs
	$(GHCI) $(GHCI_FLAGS) $*

hugs-%: %.hs
	$(HUGS) $(HUGS_FLAGS) $*

tests: all
	./$(EXEC) -tests ../tests

clean:
	rm -f *.hi *.o *.prof

cleaner: clean
	rm -f $(EXEC)

manual: all
	./$(EXEC) -manual ../doc
	$(MAKE) -C ../doc -f `pwd`/Makefile OmegaManual.ps

OmegaManual.ps: version.tex OmegaManual.tex
	latex$(EXT) OmegaManual.tex
	bibtex$(EXT) OmegaManual
	latex$(EXT) OmegaManual.tex && latex$(EXT) OmegaManual.tex
	dvips$(EXT) OmegaManual
	- dvipdf$(EXT) OmegaManual

update:
	$(SVN) update ..

