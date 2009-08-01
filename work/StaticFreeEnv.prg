import "LangPrelude.prg"

prop Free :: Tag ~> Row Tag * ~> * where
  Klar :: Free t {}r
  Mehr :: DiffLabel t t' -> Free t r -> Free t {t'=a;r}r
 deriving List(f)

notMentionedIn :: Label a -> Record sh -> Maybe (Free a sh)
notMentionedIn l {} = Just $ Klar
notMentionedIn l {m=v; r} = do
                            diff <- case sameLabel l m of
                                    R x -> Just x
      	      	      	      	    _ -> Nothing
                            r' <- notMentionedIn l r
                            return $ Mehr diff r'
                       where monad maybeM

Just test1 = `a `notMentionedIn` {`g=7, `h='a'}

##test "`a occurs in head position"
  Just test2 = `a `notMentionedIn` {`g=7, `a='a'}

##test "`a occurs in second position"
  Just test3 = `a `notMentionedIn` {`a=7, `b='b'}


data Environment :: Row Tag * ~> * where
  Empty :: Environment {}r
  Extend :: Free t s => Label t -> a -> Environment s -> Environment {t=a;s}r
 deriving Record(e)

verifyEnv :: Record sh -> Maybe (Environment sh)
verifyEnv {} = Just {}e
verifyEnv {l=v; r} = do
                     l' <- l `notMentionedIn` r
                     r' <- verifyEnv r
                     return {l=v; r'}e
                 where monad maybeM

Just test4 = verifyEnv {`g=7, `a='a', `h="hey"}

##test "`g occurs twice"
  Just test5 = verifyEnv {`g=7, `a='a', `g="2"}
