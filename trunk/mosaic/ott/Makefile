.PHONY: clean

%.tex: %.ott
	ott -i $< -o $@

%.pdf: %.tex
	pdflatex $<


clean:
	rm -f *.log *.tex *.pdf *.aux
