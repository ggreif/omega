
interesting && /\ <\/div>/ {
    interesting = 0
    next
}

interesting {
    gsub(/<h[1-9]>/, "\n&\n")
    gsub(/<\/h[1-9]>/, "\n&\n")
    print
    next
}

/\ <div class="vt" id="wikimaincol">/ {
     interesting = 1
     next
}