BEGIN {
    interesting = 1
}

skipScript && /<\/script>/ {
  skipScript = 0
  next
}

skipScript {
  next
}

/<script type="text\/javascript" charset="utf-8">/ {
  print "  <script src='http://www.w3.org/Talks/Tools/Slidy2/scripts/slidy.js' charset='utf-8' type='text/javascript'></script>"
  skipScript = 1
  next
}

/<style type="text\/css">/ {
  styleEncountered++
}

styleEncountered == 2 && /<\/style>/ {
  print "  <link rel='stylesheet' type='text/css' media='screen, projection, print' href='http://www.w3.org/Talks/Tools/Slidy2/styles/slidy.css' />"
  styleEncountered = 3
}

styleEncountered == 2 {
  next
}


{
    sub(/<title>Haskell: Functional Programming, Solid Code, Big Data<\/title>/, "<title>Intro \\&ldquo;Functional Programming\\&rdquo;</title>")
    sub(/<meta name="date" content="2011-09-18" \/>/, "<meta name='date' content='2011-10-19' />")
    sub(/<meta name="author" content="Bryan O'Sullivan" \/>/, "<meta name='author' content='Gabor Greif' />\n  <meta name='duration' content='45' />\n  <link type='text/css' rel='stylesheet' href='http://www.gstatic.com/codesite/ph/13841197563397998716/css/ph_detail.css' />\n  <meta name='copyright' content='Copyright \\&#169; 2011 Gabor Greif' />")
}

/^<body>/ {
    interesting = 0
    print
    next
}

interesting {
    print
    next
}

