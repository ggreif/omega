
-- primitive Susy :: Int
-- primitive linda :: Int -> Int

primitive import (parseChar, parseInt)

parseM = Monad returnParser bindParser failParser
