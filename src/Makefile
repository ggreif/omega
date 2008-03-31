MAIN             = Main
EXEC             = omega.exe
GHC              = ghc
GHCI             = ghci
GHC_FLAGS        = -auto-all  $(GHC_FLAGS_COMMON)
GHCI_FLAGS       = $(GHC_FLAGS_COMMON)
GHC_FLAGS_COMMON = -fglasgow-exts -fallow-undecidable-instances
HUGS             = hugs
HUGS_FLAGS       = -98 -P:../Lib:../Lib/Parser

.PHONY: all clean

all: *.hs
	$(GHC) $(GHC_FLAGS) -o $(EXEC) --make $(MAIN)

%: %.hs *.hs
	$(GHC) $(GHC_FLAGS) --make $*

ghci-%: %.hs
	$(GHCI) $(GHCI_FLAGS) $*

hugs-%: %.hs
	$(HUGS) $(HUGS_FLAGS) $*

clean:
	rm -f *.hi *.o *.prof
manual: all
	./$(EXEC) -manual ../doc
	cd ../doc && latex OmegaManual.tex
	cd ../doc && bibtex.exe OmegaManual
	cd ../doc && latex OmegaManual.tex && latex OmegaManual.tex
	cd ../doc && dvips.exe OmegaManual





