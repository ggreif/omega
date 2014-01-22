LATEX-FILES = $(wildcard *.tex)

.PHONY: all clean, view

all: $(LATEX-FILES:%.tex=%.pdf)

view: $(LATEX-FILES:%.tex=%.pdf)
	acroread $< &

%.pdf: %.tex
	pdflatex $< > /dev/null && sha1sum $@ > $(@:%.pdf=%.sum)

clean:
	rm -f *.log *.tex *.pdf *.aux
