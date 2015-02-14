OTTFILES = $(wildcard *.ott)

.PHONY: all clean

all: $(OTTFILES:%.ott=%.pdf)

%.tex: %.ott
	ott -i $< -o $@

%.pdf: %.tex
	pdflatex -interaction=nonstopmode $< > /dev/null

clean:
	rm -f *.log *.tex *.pdf *.aux
