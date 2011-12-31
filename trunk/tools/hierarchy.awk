BEGIN {
    heading = 0
}

hunt && /class="section_anchor">/ {
    hier[heading] = $0
    sub(/<a name="[^"]*"><\/a>/, "", hier[heading])
    sub(/<a href=".*" class="section_anchor"><\/a>/, "", hier[heading])

    if (heading == 2)
    {
      here = "&sdot;&nbsp;" hier[heading]
    }
    else if (heading == 3)
    {
      here = "&ndash;&nbsp;" hier[heading]
    }
    else if (heading >= 4)
    {
      here = "&mdash;&nbsp;" hier[heading]
    }
    else
    {
      here = hier[heading]
    }

    if (slide) print "</div>" 
    print "<div class='slide'>"
    slide = 1
    if (heading > 1) {
      print "<h1 style='display: none;'>" here "</h1>"
    }
    for (i=1; i < heading; ++i) {
      print "<h" i " style='color: #C0C0C0;'>" hier[i] "</h" i ">"
    }
    print "<h" heading ">" hier[heading]
    hunt = 0
    next
}

## this is for twiki conventions
hunt && heading && /^<a\ name="/ {
    hier[heading] = $0
    sub(/<a name="[^"]*"><\/a>/, "", hier[heading])

    if (heading == 2)
    {
      here = "&sdot;&nbsp;" hier[heading]
    }
    else if (heading == 3)
    {
      here = "&ndash;&nbsp;" hier[heading]
    }
    else if (heading >= 4)
    {
      here = "&mdash;&nbsp;" hier[heading]
    }
    else
    {
      here = hier[heading]
    }

    if (slide) print "</div>" 
    print "<div class='slide'>"
    slide = 1
    if (heading > 1) {
      print "<h1 style='display: none;'>" here "</h1>"
    }
    for (i=1; i < heading; ++i) {
      print "<h" i " style='color: #C0C0C0;'>" hier[i] "</h" i ">"
    }
    print "<h" heading ">" hier[heading]
    hunt = 0
    next
}


/<h1>/ {
    heading = 1
    hunt = 1
    next
}

/<\/h[1-9]>/ {
    heading = 0
    print
    next
}

/<h2>/ && heading == 0 {
    heading = 2
    hunt = 1
    next
}

/<h3>/ && heading == 0 {
    heading = 3
    hunt = 1
    next
}

/<h4>/ && heading == 0 {
    heading = 4
    hunt = 1
    next
}

{
  gsub(/<p>/, "\n&\n")
  print
}

END {
    if (slide) print "</div>"
}
