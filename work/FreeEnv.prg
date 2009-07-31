-- import "LangPrelude.prg"

data Shape :: *1 where
  Vanish :: Shape
  Assoc :: Tag ~> * ~> Shape ~> Shape
 deriving Record(s)

data Env :: Shape ~> * where
  Empty :: Env Vanish
  Extend :: Label t -> a -> Env s -> Env (Assoc t a s)
 deriving Record(e)

data Free :: Tag ~> Shape ~> * where
  Klar :: Label t -> Free t Vanish
  -- Klar :: Label t -> Env Vanish -> Free t Vanish
  Mehr :: Label t -> DiffLabel t t' -> Free t r -> Free t {t'=a;r}s
-- deriving List(f)

-- diffAB' = let R x = sameLabel `a `b in x
diffAB = case sameLabel `a `b of
         R x -> x

notMentionedIn :: Label a -> Env sh -> Maybe (Free a sh)
notMentionedIn l Empty = Just $ Klar l
notMentionedIn l {m=v; r}e = case sameLabel l m of
                             L _ -> Nothing
                             R diff -> case notMentionedIn l r of
                                       Nothing -> Nothing
                                       Just r' -> Just $ Mehr l diff r'
