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

### TODO:
#  <link rel="stylesheet" type="text/css" media="screen, projection, print" href="http://www.w3.org/Talks/Tools/Slidy2/styles/slidy.css" /> 


/<script type="text\/javascript" charset="utf-8">/ {
  print "  <script src='http://www.w3.org/Talks/Tools/Slidy2/scripts/slidy.js' charset='utf-8' type='text/javascript'></script>"
  skipScript = 1
  next
}

{
    sub(/<title>Haskell: Functional Programming, Solid Code, Big Data<\/title>/, "<title>Intro \\&ldquo;Functional Programming\\&rdquo;</title>")
    sub(/<meta name="date" content="2011-09-18" \/>/, "<meta name='date' content='2011-10-19' />")
    sub(/<meta name="author" content="Bryan O'Sullivan" \/>/, "<meta name='author' content='Gabor Greif' />\n  <meta name='duration' content='45' />")
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

