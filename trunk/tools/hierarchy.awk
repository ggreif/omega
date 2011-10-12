BEGIN {
    heading = 0
}

hunt && /class="section_anchor">/ {
    hier[heading] = $0
    sub(/<a name="[^"]*"><\/a>/, "", hier[heading])
    sub(/<a href=".*" class="section_anchor"><\/a>/, "", hier[heading])
    if (slide) print "</div>" 
    print "<div class='slide'>"
    slide = 1
    if (heading > 1) {
	print "<h1 style='display: none;'>" hier[heading] "</h1>"
    }
    for (i=1; i < heading; ++i) {
	print "<h" i " style='color: #C0C0C0;'>" hier[i] "</h" i ">"
    }
    print "<h" heading ">" hier[heading]
    hunt = 0
    next
}

/<h1>/ {
    #print "<div class=\"slide\">"
    heading = 1
    hunt = 1
    #print
    next
}

/<\/h[1-9]>/ {
    heading = 0
    print
    next
}

/<h2>/ && heading == 0 {
    #print "</div>"
    #print "<div class=\"slide\">"
    #print "<h1 style=\"display: none;\">" hier[1] "</h1>"
    heading = 2
    hunt = 1
    #print
    next
}

/<h3>/ && heading == 0 {
    #print "</div>"
    #print "<div class=\"slide\">"
    #print "<h1 style=\"display: none;\">" hier[1] "</h1>"
    #print "<h2 style=\"display: none;\">" hier[2] "</h2>"
    heading = 3
    hunt = 1
    #print
    next
}

/<h4>/ && heading == 3 {
    heading = 4
    hunt = 1
    #print
    next
}