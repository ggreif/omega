
NAME = Main
REFS = references.bib

all: $(NAME).ps prgs
	@echo "done"

prgs: BinomialHeap.prg CPS.prg

$(NAME).pdf: $(NAME).tex
	pdflatex $(NAME).tex

$(NAME).ps: $(NAME).dvi
	dvips -tletter -o $(NAME).ps $(NAME)

$(NAME).dvi: fig.1 $(NAME).bbl $(NAME).tex
	latex $(NAME)

$(NAME).tex: $(NAME).lhs BinomialHeap.lhs CPS.lhs HeapAppendix.lhs
	lhs2TeX --poly $(NAME).lhs > $(NAME).tex

$(NAME).bbl: $(REFS)
	make $(NAME).tex
	latex $(NAME)
	-bibtex $(NAME)
	latex $(NAME)

fig.1: fig.mp
	mpost fig.mp

view:	$(NAME).ps
	gv -watch $(NAME).ps&

CPS.prg: CPS.lhs
	runhugs lhs2prg CPS.lhs > CPS.prg

BinomialHeap.prg: BinomialHeap.lhs HeapAppendix.lhs
	runhugs lhs2prg BinomialHeap.lhs > BinomialHeap.prg
	runhugs lhs2prg HeapAppendix.lhs >> BinomialHeap.prg

clean:
	rm -f $(NAME).tex $(NAME).aux $(NAME).log $(NAME).dvi fig.log

spotless: clean
	rm -f BinomialHeap.prg CPS.prg \
		$(NAME).ps $(NAME).bbl $(NAME).blg \
		fig.[1-9] fig.[1-9][0-9]

