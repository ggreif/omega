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

## DEVDIR: where is the omega/ dir?
DEVDIR           = $(HOME)
DISTR            = $(DEVDIR)/Omega/distr

## unset these to be serious
##
JUST-TEST = echo
HACKAGE-SERIOUS = --check

## Hackage credentials
##
HACKAGE-USER = GaborGreif
HACKAGE-PASSW = jXXXX

.PHONY: all cabal cabal-check cabal-pack omega-pack \
        tests regressions clean cleaner manual update

all: *.hs
	$(GHC) $(GHC_FLAGS) -o $(EXEC) --make $(MAIN)

cabal:
	- rm -r $(DISTR)
	cd ../util && runhaskell BuildDistr.hs "$(DEVDIR)"
	cd $(DISTR) && cabal configure -v && cabal build -v

cabal-check:
	@ grep -i version $(DISTR)/* | grep "1\." | grep -v "Open Font License" \
	| grep -v "distr/OmegaManual.ps" \
	| grep -v "Omega Interpreter: version 1.5.3"
	@ grep /tags/ $(DISTR)/*     | grep "1\."
	@ grep tag: $(DISTR)/*       | grep "1\."
	@ grep "201" $(DISTR)/*       | grep -v "2002-2013" | grep -v "CEST 2013" \
	| grep -v "distr/OmegaManual.ps"
	@ echo
	@ echo ":q" | $(DISTR)/dist/build/omega/omega || true
	@ echo
	@ cd $(DISTR) && cabal check

cabal-pack:
	cd $(DISTR) && cabal sdist -v

cabal-upload:
	@ $(JUST-TEST) cabal upload $(HACKAGE-SERIOUS) --username=$(HACKAGE-USER) --password=$(HACKAGE-PASSW) $(DISTR)/dist/omega-1.5.3.tar.gz

omega-pack:
	cd $(DISTR)/.. \
	&& zip -v -r Omega153 distr -l -x \*.cabal distr/Setup.hs \*.pdf \*.ps distr/dist/\* \
	&& zip -v -u Omega153 distr/*.pdf distr/*.ps \
	&& ls -l Omega1*

omega-tag:
	$(JUST-TEST) $(SVN) cp -m "tag Omega 1.5.3" ^/trunk ^/tags/omega-1.5.3
	$(JUST-TEST) $(SVN) switch ^/tags/omega-1.5.3/src/Version.hs Version.hs
	$(JUST-TEST) $(SVN) ci -m "update version to match distribution" Version.hs
	$(JUST-TEST) $(SVN) switch ^/trunk/src/Version.hs Version.hs

%: %.hs *.hs
	$(GHC) $(GHC_FLAGS) --make $*

ghci-%: %.hs
	$(GHCI) $(GHCI_FLAGS) $*

hugs-%: %.hs
	$(HUGS) $(HUGS_FLAGS) $*

tests: all
	./$(EXEC) -tests ../tests

regressions: all
	./$(EXEC) -tests ../tests 2>&1 | awk -f ../tests/filter.awk

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
	dvips$(EXT) -o $@ OmegaManual
	- dvipdf$(EXT) OmegaManual

update:
	$(SVN) update ..

