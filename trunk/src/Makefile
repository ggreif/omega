MAIN             = Main
EXT              = .exe
EXEC             = omega$(EXT)
GHC              = ghc
GHCI             = ghci
GHC_FLAGS        = -auto-all $(GHC_OPT_FLAGS) $(GHC_FLAGS_COMMON)
GHCI_FLAGS       = $(GHC_FLAGS_COMMON)
GHC_FLAGS_COMMON = 
GHC_OPT_FLAGS    = 
HUGS             = hugs
HUGS_FLAGS       = -98 -P:../Lib:../Lib/Parser
SVN              = svn
DISTR            = ~/Omega/distr/

.PHONY: all cabal cabal-check tests clean cleaner manual update

all: *.hs
	$(GHC) $(GHC_FLAGS) -o $(EXEC) --make $(MAIN)

cabal:
	rm -r $(DISTR)
	cd ../util && runhaskell BuildDistr.hs
	cd $(DISTR) && cabal configure -v && cabal build -v

cabal-check:
	@ grep -i version $(DISTR)/* | grep "1\." | grep -v "Open Font License"
	@ grep /tags/ $(DISTR)/*     | grep "1."
	@ grep tag: $(DISTR)/*       | grep "1."
	@ echo
	@ cd $(DISTR) && cabal check

%: %.hs *.hs
	$(GHC) $(GHC_FLAGS) --make $*

ghci-%: %.hs
	$(GHCI) $(GHCI_FLAGS) $*

hugs-%: %.hs
	$(HUGS) $(HUGS_FLAGS) $*

tests: all
	./$(EXEC) -tests ../tests

%.prg: all
	./$(EXEC) $@

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

