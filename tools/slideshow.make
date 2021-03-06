all: slides.html

.PHONY: again clean cleaner

clean:
	rm -f slides.html tslides.html *.html.top *.html.content 

cleaner: clean
	rm -f wiki.html twiki.html slidy.html

again: clean
	rm -f wiki.html
	$(MAKE) -f slideshow.make all

slidy.html:
	curl "http://bos.github.com/strange-loop-2011/slides/slides.html" > $@

wiki.html:
	curl "http://code.google.com/p/omega/wiki/ALTATalk" > $@

slidy.html.top: slidy.html
	awk -f slidy.awk < $(<) > $@

wiki.html.content: wiki.html
	awk -f wiki.awk < $(<) | awk -f hierarchy.awk > $@

slides.html: slidy.html.top slides.html.cover wiki.html.content slides.html.tail
	cat $(^) | awk -f backgrounds.awk > $@

twiki.html:
	curl "http://twiki.org/cgi-bin/view/TWiki/TextFormattingRules" > $@

twiki.html.content: twiki.html
	awk -f twiki.awk < $(<) | awk -f hierarchy.awk > $@

tslides.html: slidy.html.top slides.html.cover twiki.html.content slides.html.tail
	cat $(^) > $@

