/fails as expected\.$/ {next}
/successfully loaded$/ {next}
/^ *<-.*loaded\.$/ {next}
/^->Loading import/ {next}
/^loading / {next}

# empty lines are dull
#
/^ *$/ {next}

{print}
