-- primitives for parsing

-- monadic primitives
--
primitive import (returnParser, bindParser, failParser)
parseM = Monad returnParser bindParser failParser

-- running
--
primitive import (runParser)

-- combinators
--
primitive import ((<|>), (<?>))

-- parsers for basic things
--
primitive import (char, {-satisfy,-} string, many, parens
                 , try, between, sepBy)


-- parsers for Omega literals
--
primitive import ( parseChar, parseInt, parseString
                 , parseIdentifier{-, parseSymbol-} )

