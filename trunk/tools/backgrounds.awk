BEGIN {
  slidecount = 0
}


/<div class="slide cover title">/ {
  print "<div class='background cover'>"
  print "  <img style='width: 100%; float:right' src='ALTA_Flower.png' alt='ALTA flower' />"
  print "</div>"
  print ""
}

/<div class='slide'>/ {
  slidecount++
  if (slidecount == 2)
  {
    print "<div class='background haskell'>"
    print "  <img style='float:right' src='http://www.haskell.org/wikiupload/4/4a/HaskellLogoStyPreview-1.png' alt='Haskell logo' />"
    print "</div>"
    sub(/slide/, "slide haskell")
  }
}

{ print }
