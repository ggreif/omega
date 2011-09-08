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

-- parsers for Omega literals
primitive import (parseChar, parseInt)

