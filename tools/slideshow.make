all: slides.html

.PHONY: again clean

clean:
	- rm *.html.top *.html.content 

again: clean
	$(MAKE) -f slideshow.make all

slidy.html:
	curl "http://bos.github.com/strange-loop-2011/slides/slides.html" > $@

wiki.html:
	curl "http://code.google.com/p/omega/wiki/ALTATalk" > $@

slidy.html.top: slidy.html
	awk -f slidy.awk < $(<) > $@

wiki.html.content: wiki.html
	awk -f wiki.awk < $(<) | awk -f hierarchy.awk > $@

slides.html: slidy.html.top slides.html.cover wiki.html.content
	cat $(^) > $@
	echo "</body>" >> $@
	echo "</html>" >> $@