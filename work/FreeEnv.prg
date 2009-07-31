-- import "LangPrelude.prg"
{-
data Shape :: *1 where
  Vanish :: Shape
  Assoc :: Tag ~> * ~> Shape ~> Shape
 deriving Record(s)

data Env :: Shape ~> * where
  Empty :: Env Vanish
  Extend :: Label t -> a -> Env s -> Env (Assoc t a s)
 deriving Record(e)
-}

data Free :: Tag ~> Row Tag * ~> * where
  Klar :: Label t -> Free t {}r
  Mehr :: Label t -> DiffLabel t t' -> Free t r -> Free t {t'=a;r}r
-- deriving Record(f)

-- diffAB' = let R x = sameLabel `a `b in x -- see issue 65
diffAB = case sameLabel `a `b of
         R x -> x

notMentionedIn :: Label a -> Record sh -> Maybe (Free a sh)
notMentionedIn l {} = Just $ Klar l
notMentionedIn l {m=v; r} = case sameLabel l m of
                            L _ -> Nothing
                            R diff -> case notMentionedIn l r of
                                      Nothing -> Nothing
                                      Just r' -> Just $ Mehr l diff r'

Just test1 = `a `notMentionedIn` {`g=7, `h='a'}
Nothing = `a `notMentionedIn` {`g=7, `a='a'}
Nothing = `a `notMentionedIn` {`a=7, `b='b'}

