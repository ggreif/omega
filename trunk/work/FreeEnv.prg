import "LangPrelude.prg"

data Free :: Tag ~> Row Tag * ~> * where
  Klar :: Label t -> Free t {}r
  Mehr :: Label t -> DiffLabel t t' -> Free t r -> Free t {t'=a;r}r
-- deriving Record(f)

notMentionedIn :: Label a -> Record sh -> Maybe (Free a sh)
notMentionedIn l {} = Just $ Klar l
notMentionedIn l {m=v; r} = do
                            diff <- case sameLabel l m of
                                    R x -> Just x
      	      	      	      	    _ -> Nothing
                            r' <- notMentionedIn l r
                            return $ Mehr l diff r'
                       where monad maybeM

Just test1 = `a `notMentionedIn` {`g=7, `h='a'}
Nothing = `a `notMentionedIn` {`g=7, `a='a'}
Nothing = `a `notMentionedIn` {`a=7, `b='b'}

