
copy = `copy

test = HideLabel copy

HideLabel y = newLabel "x"

{- 
f x = case sameLabel y `a of
        R (t@Eq) -> t
        L _ -> error "BAD"
  where (HideLabel y) = newLabel x
  -}