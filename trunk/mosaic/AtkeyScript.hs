-- this mosaic explores the way laid out by Robert Atkey in
--  http://bentnib.org/posts/2015-04-19-algebraic-approach-typechecking-and-elaboration.html

{-# LANGUAGE TypeOperators #-}

data Type = A | B | C | Type :-> Type deriving Eq

type TypeChecker = [Type] -> Maybe Type

-- a TypeChecker is basically something that maybe has a type in a context
--   (e.g. a Term)

var :: Int -> TypeChecker
var i ctxt = Just $ ctxt !! i

lam :: Type -> TypeChecker -> TypeChecker
lam = undefined

app :: TypeChecker -> TypeChecker -> TypeChecker
app = undefined



