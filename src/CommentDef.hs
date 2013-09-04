module CommentDef (cLine,cStart,cEnd,nestedC) where

-----------------------------------------------------------
-- In order to do layout, we need to "skip white space"
-- We need combinators that compute white space. Thus we
-- need to know how comments are formed. These constants
-- let us compute a whitespace parser. They fields in
-- TokenDef are derived from these definitions

-- Haskell Style
cStart = "{-"   -- (commentStart tokenDef)
cEnd   = "-}"   -- (commentEnd tokenDef)
cLine  = "--"   -- (commentLine tokenDef)
nestedC = True  -- (nestedComment tokenDef)
