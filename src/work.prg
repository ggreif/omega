
copy = `copy

test = HideLabel copy

HideLabel y = newLabel "x"


f x = case sameLabel y `a of
        L (t@Eq) -> t
        R _ -> error "BAD"
  where (HideLabel y) = newLabel x
  