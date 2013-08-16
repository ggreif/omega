-- See: http://en.wikipedia.org/wiki/Normalisation_by_evaluation
-- and also http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.39.2361
-- almost there: http://www.cs.nott.ac.uk/~txa/publ/flops04.pdf
--       slides: http://www.cs.nott.ac.uk/~txa/talks/flops-slides.pdf
-- other slides: http://cs.ioc.ee/~tarmo/tsem08/abel-slides.pdf
--     by Fiore: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.130.1867
--     and Abel: http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.278.4776
--
import "../src/LangPrelude.prg" (listM,Monad,compose,const)

monad listM

-- abstract syntax -------------------------------------------------------------

data Ty :: *0 ~> *0 where
   Bool :: Ty Bool
   Arr :: Ty a -> Ty b -> Ty (a -> b)

data Var :: *0 ~> *0 ~> *0 where
   ZVar :: Var (h,t) t
   SVar :: Var h t -> Var (h,s) t

data Exp :: *0 ~> *0 ~> *0 where
   Var :: Var g t -> Exp g t
   Lam :: Ty a -> Exp (g,a) b -> Exp g (a -> b)
   App :: Exp g (s -> t) -> Exp g s -> Exp g t
   If :: Exp g Bool -> Exp g t -> Exp g t -> Exp g t
   ETrue :: Exp g Bool
   EFalse :: Exp g Bool

-- smart constructors ----------------------------------------------------------
lamE :: Ty s -> (Exp (g,s) s -> Exp (g,s) t) -> Exp g (s -> t)
lamE s f = Lam s (f (Var ZVar))

ifE :: Exp g Bool -> Exp g t -> Exp g t -> Exp g t
ifE t ETrue EFalse = t
ifE t e e' = if eqE e e' then e else If t e e'

-- boring equality tests -------------------------------------------------------
eqB :: BoxExp t -> BoxExp s -> Bool
eqB (Box e) (Box e') = eqE e e'

eqE :: Exp g t -> Exp h s -> Bool
eqE (Var x) (Var y) = eqV x y
eqE (Lam s e) (Lam s' e') = eqT s s' && eqE e e'
eqE (App e1 e2) (App e1' e2') = eqE e1 e1' && eqE e2 e2'
eqE (If e1 e2 e3) (If e1' e2' e3') = eqE e1 e1' && (eqE e2 e2' && eqE e3 e3')
eqE ETrue ETrue = True
eqE EFalse EFalse = True
eqE _ _ = False

eqT :: Ty t -> Ty s -> Bool
eqT (Arr s t) (Arr s' t') = eqT s s' && eqT t t'
eqT Bool Bool = True
eqT _ _ = False

eqV :: Var g t -> Var h s -> Bool
eqV (SVar x) (SVar y) = eqV x y
eqV ZVar ZVar = True
eqV _ _ = False

-- evaluation ------------------------------------------------------------------
var :: Var g t -> g -> t
var ZVar     (_,t) = t
var (SVar x) (h,s) = var x h

exp :: Exp g t -> g -> t
exp (Var x)    g = var x g
exp (Lam _ e)  g = \a -> exp e (g,a)
exp (App e e') g = exp e g (exp e' g)
exp ETrue      g = True
exp EFalse     g = False
exp (If c t e) g = if exp c g then exp t g else exp e g

-- type inference --------------------------------------------------------------


data TyEnv :: *0 ~> *0 where
   Cons :: Ty t -> TyEnv h -> TyEnv (h,t)
   Nil :: TyEnv g

infer :: TyEnv g -> Exp g t -> Ty t
infer g (Var x)         = inferVar g x
infer g (Lam t e)       = Arr t (infer (Cons t g) e)
infer g (App e e')      = case infer g e of Arr _ t -> t
infer g ETrue           = Bool
infer g EFalse          = Bool
infer g (If _ e _)      = infer g e

inferVar :: TyEnv g -> Var g t -> Ty t
inferVar (Cons t h) (SVar x) = inferVar h x
inferVar (Cons t h) (ZVar)   = t

-- tree monad ------------------------------------------------------------------

data Tree a = Val a | Choice (Tree a) (Tree a)
-- doesn't yet force trees to be fully balanced:
--      Val :: a -> Tree a Z
--      Choice :: Tree a n -> Tree a n -> Tree a (S n)

treeM = Monad Val bind error
  where bind (Val a) f = f a
        bind (Choice l r) f = Choice (bind l f) (bind r f)

tmap f x = do a <- x; return (f a)
  where monad treeM

flatten t = fl t []
 where
   fl (Val a)      k = a:k
   fl (Choice l r) k = fl l (fl r k)


-- quote & friends -------------------------------------------------------------

-- for values --------------------------
enumV           :: Ty t -> Tree t
questionsV      :: Ty t -> [t -> Bool]


enumV Bool      = Choice (Val True) (Val False)
enumV (Arr s t) = mkEnum (questionsV s) (enumV t)
 where
   monad treeM
   mkEnum [] t = tmap const t
   mkEnum (q:qs) es = do
                   f1 <- mkEnum qs es
                   f2 <- mkEnum qs es
                   return (\d -> if q d then f1 d else f2 d)

questionsV Bool         = return (\x -> x)
questionsV (Arr s t)    = do
                          d <- flatten (enumV s)
                          q <- questionsV t
                          return (\f -> q (f d))

-- for expressions ---------------------
enumE           :: Ty t -> Tree (Exp g t)
questionsE      :: Ty t -> [Exp g t -> Exp g Bool]

enumE Bool      = Choice (Val ETrue) (Val EFalse)
enumE (Arr s t) = tmap (lamE s) (mkEnumE (questionsE s) (enumE t))
 where
   monad treeM
   mkEnumE [] t = tmap const t
   mkEnumE (q:qs) es = do
                        f1 <- mkEnumE qs es
                        f2 <- mkEnumE qs es
                        return (\d -> ifE (q d) (f1 d) (f2 d))

questionsE Bool         = return (\x -> x)
questionsE (Arr s t)    = do
                          d <- flatten (enumE s)
                          q <- questionsE t
                          return (\f -> q (App f d))

-- should be
--      find (List (Exp g Bool) n) -> Tree (Exp g a) n -> Exp g a
find :: [Exp g Bool] -> Tree (Exp g a) -> Exp g a
find []         (Val a)         = a
find (b:bs)     (Choice l r)    = ifE b (find bs l) (find bs r)
find _          _               = error "bad arguments to find"

quote :: Ty t -> t -> Exp g t
quote Bool      t = case t of True -> ETrue; False -> EFalse
quote (Arr s t) f = lamE s (\e -> find (do q <- questionsE s; return (q e))
                                        (tmap (quote t . f) (enumV s)))

-- normalization (by evaluation) -----------------------------------------------
data BoxExp t = Box (forall g. Exp g t)

normalize :: Ty t -> BoxExp t -> BoxExp t
normalize s (Box e) = Box (quote s (exp e ()))

-- examples --------------------------------------------------------------------
b2b = Arr Bool Bool
b22b = Arr b2b b2b
zero = Var ZVar
one = Var (SVar ZVar)
once   = Box (Lam b2b (Lam Bool (App one zero)))
twice  = Box (Lam b2b (Lam Bool (App one (App one zero))))
thrice = Box (Lam b2b (Lam Bool (App one (App one (App one zero)))))

test = [ eqB (nf b22b thrice) (nf b22b once)
       , eqB (nf b22b twice)  (nf b22b once)]
  where nf = normalize
