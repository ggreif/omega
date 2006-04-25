MAIN             = Main
EXEC             = omega.exe
GHC              = ghc
GHCI             = ghci
GHC_FLAGS        = -O -auto-all $(GHC_FLAGS_COMMON)
GHCI_FLAGS       = $(GHC_FLAGS_COMMON)
GHC_FLAGS_COMMON = -fglasgow-exts -package lang -fallow-undecidable-instances -id:../Lib/Parser -id:../Lib
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

clean :
	rm -f *.hi *.o *.prof 
