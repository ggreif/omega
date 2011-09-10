BEGIN {
  print "%TCIDATA{Version=5.00.0.2606}";
  print "%TCIDATA{LaTeXparent=0,0,classes.tex}";
  print "                      ";
  print "";
  print "%%%%% BEGINNING OF DOCUMENT BODY %%%%%";
  print "% html: Beginning of file: `clean.html'";
  print "% DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01//EN\"";
  print "%  This is a (PRE) block.  Make sure it's left aligned or your toc title will be off. ";
  print "";
  quoting = 0;
  itemizing = 0;
  coding = 0;
}

END {
  print "% html: End of file: `clean.html'";
  print "";
  print "%%%%% END OF DOCUMENT BODY %%%%%";
  print "% In the future, we might want to put some additional data here, such";
  print "% as when the documentation was converted from wiki to TeX.";
  print "%";
}

{ origLine = $0; }

## HANDLE CODING
## make sure that control sequences are always at the front
/ *{{{/ { sub(/ */, "") }
/ *}}}/ { sub(/ */, "") }

!coding && /^{{{/ {

  if (quoting) {
    print "\\end{quotation}";
    print ""
    quoting = 0;
  }

  print "\\begin{verbatim}";
  coding = 1;
  next;
}

coding && /^}}}/ {
  sub(/}}}.*$/, "", origLine);
  if (origLine) {
    print "{\\small " origLine
    print "}"
  }
  print "\\end{verbatim}";
  print ""
  coding = 0;
  next;
}

coding {
  sub(/^/, "{\\small ");
  print;
  print "}";
  next;
}

## NO CODING BELOW THIS POINT
coding { print "###code???####"; next; }


## pragmas do not count
/^\#labels/ {
  next;
}


## make sure that control sequences are always at the front
/^ *=/ { sub(/^ *=/, "=") }

## check itemness
{ inItem = 0 }
/^   *\*/ {
  inItem = 1
  ## print " ########## ITEM"
}

itemizing && !inItem {
  print "\\end{itemize}";
  print "";
  itemizing = 0;
}



## quoting stops when item appears
## or not indented any more
quoting && (inItem || !/^ /) {
  print "\\end{quotation}";
  print ""
  quoting = 0;
}

## empty lines do not count
/^ *$/ {
  next;
}

/`/ {
  line = $0;
  sub(/`/, "\\texttt{", line);
  sub(/`/, "}", line);
  $0 = line
}

/^==/ {
  sub(/^==/, "\\subsection*{");
  sub(/==/, "}");
  print;
  next;
}

/^=/ {
  sub(/^=/, "\\section*{");
  sub(/=/, "}");
  print;
  print "";
  print "\\label{f0}";
  next;
}

quoting && /^ / {
  sub(/^ /, "");
  print;
  next;
}

!itemizing && inItem {
  print "\\begin{itemize}";
  itemizing = 1;
}

itemizing && inItem {
  sub(/^   *\*/, "\\item");
  print;
  print "";
  next;
}


/^ / {
  print ""
  print "\\begin{quotation}";
  quoting = 1;
  sub(/^ /, "");
  print;
  next;
}



{ print }
