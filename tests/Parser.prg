import "../src/LangPrelude.prg" (parseM)

monad parseM

verify (Just 67) = "ok"

t1 = verify $ runParser p "42 25"
       where p = do a <- parseInt
                    b <- parseInt
                    return (a + b)

