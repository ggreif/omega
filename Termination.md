# Introduction #

One of the big gaps in Ωmega's feature set is that the functions that create proof objects are not checked for termination. There is nothing that would hinder one to lie in a proof by mentioning _undefined_ or leave off a case leg or recurse indefinitely. This makes the whole logic fragment unreliable.

Many researchers have put their teeth into this subject and some practical solutions emerge. The most promising solutions seem to pick _sized types_ as a vehicle. The essence of this approach is that terminating algorithms (after all) recurse on a smaller portion of the data they have been invoked with.

# Literature #

Here comes a selection of references to some current ideas in type based termination checking.

  * [Gilles Barthe et al. - 2004](http://repositorium.sdum.uminho.pt/bitstream/1822/1977/1/TBterm.pdf)
  * [Gilles Barthe et al. - 2008](http://perso.ens-lyon.fr/colin.riba/papers/exprod.pdf)
  * [Andreas Abel - 2008](http://arxiv.org/pdf/0804.0876v2)

_See also references at the end of above papers._

There is a [very nice blog post](http://personal.cis.strath.ac.uk/~raa/posts/2011-04-28-folds-and-induction.html) from Robert Atkey which explains structural induction (not coinduction) and references many interesting discussions and papers.

# Slide Shows #

  * http://www.tcs.informatik.uni-muenchen.de/~abel/talkITU07.pdf
  * http://www.tcs.informatik.uni-muenchen.de/~mhofmann/appsem2//LectureNotes/barthe-lec3.pdf

# Implementation #

[Some initial work](http://code.google.com/p/omega/source/browse/trunk/work/LabelExpsWithTerminationWitnesses.prg) is checked in by Tim.