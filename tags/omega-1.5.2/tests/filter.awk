# negative tests
#
/fails as expected\.$/ {next}

# importing related
#
/successfully loaded$/ {next}
/^ *<-.*loaded\.$/ {next}
/^ *->Loading import/ {next}
/^loading / {next}
/^ *Import .* already loaded.$/ {next}

# empty lines are dull
#
/^ *$/ {next}

{print}
