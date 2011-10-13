BEGIN {
    interesting = 1
}

{
    sub(/<title>Haskell: Functional Programming, Solid Code, Big Data<\/title>/, "<title>Intro \"Functional Programming\"</title>")
    sub(/<meta name="date" content="2011-09-18" \/>/, "<meta name=\"date\" content=\"2011-10-19\" />")
    sub(/<meta name="author" content="Bryan O'Sullivan" \/>/, "<meta name=\"author\" content=\"Gabor Greif\" />")
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

