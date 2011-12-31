interesting && /^<div\ class="twikiContentFooter"/ {
    interesting = 0
    next
}

/^<h1>/ {
     interesting = 1
}

interesting {
    gsub(/<h[1-9]>/, "\n&\n")
    gsub(/<\/h[1-9]>/, "\n&\n")
    print
    next
}
