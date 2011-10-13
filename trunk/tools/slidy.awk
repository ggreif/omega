BEGIN {
    interesting = 1
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

