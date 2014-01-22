LATEX-FILES = $(wildcard *.tex)

.PHONY: all clean

all: $(LATEX-FILES:%.tex=%.pdf)

%.pdf: %.tex
	pdflatex $< > /dev/null

clean:
	rm -f *.log *.tex *.pdf *.aux
