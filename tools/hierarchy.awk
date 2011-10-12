BEGIN {
    heading = 0
}

hunt && /class="section_anchor">/ {
    hier[heading] = $0
    sub(/<a name="[^"]*"><\/a>/, "", hier[heading])
    sub(/<a href=".*" class="section_anchor"><\/a>/, "", hier[heading])
    print "#############" hier[heading]
    hunt = 0
}

/<h1>/ {
    print "<div class=\"slide\">"
    heading = 1
    hunt = 1
    print
    next
}

/<\/h[1-9]>/ {
    heading -= 1
    print
    next
}

/<h2>/ && heading == 1 {
    print "</div>"
    print "<div class=\"slide\">"
    print "<h1 style=\"display: none;\">" hier[heading] "</h1>"
    heading = 2
    hunt = 1
    print
    next
}

/<h3>/ && heading == 2 {
    heading = 3
    hunt = 1
    print
    next
}

/<h4>/ && heading == 3 {
    heading = 4
    hunt = 1
    print
    next
}