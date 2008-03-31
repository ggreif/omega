-- These are examples from the GPCE paper

import "../LangPrelude.prg" (Eq,foldr,foldl,map,compose,id)

----------
-- Units and Magnitudes (dimension analysis via type checking)

kind Unit = Pixel | Centimeter

data Mag :: Unit ~> *0 where
   Px :: Int -> Mag Pixel
   Cm :: Int -> Mag Centimeter
   
          
----------
-- Regions

data Region u = Reg (Mag u -> Mag u -> Bool)

-- basic regions
circle :: Mag u -> Region u
circle r = Reg (\x y -> leq (plus (square x) (square y)) (square r))

rect :: Mag u -> Mag u -> Region u
rect w h = Reg (\x y -> between (neg w) (plus x x) w &&
                        between (neg h) (plus y y) h)

univ :: Region u
univ = Reg (\x y -> True)

empty :: Region u
empty = Reg (\x y -> False)

-- region combinators
trans :: (Mag u,Mag u) -> Region u -> Region u
trans (a,b) (Reg f) = Reg (\x y -> f (minus x a) (minus y b))

convert :: (Mag v -> Mag u) -> Region u -> Region v
convert t (Reg f) = Reg (\x y -> f (t x) (t y))

intersect :: Region u -> Region u -> Region u
intersect (Reg f) (Reg g) = Reg (\x y -> f x y && g x y)

union :: Region u -> Region u -> Region u
union (Reg f) (Reg g) = Reg (\x y -> f x y || g x y)

draw :: Region Pixel -> IO ()
draw (Reg f) = undefined

scale = 72 -- ?

pxTOcm :: Mag Pixel -> Mag Centimeter
pxTOcm (Px i) = Cm (rem i scale)

cmTOpx :: Mag Centimeter -> Mag Pixel
cmTOpx (Cm i) = Px (i*scale)

-- overloaded operators on Magnitudes. leave these out in the writeup
neg :: Mag u -> Mag u
neg (Px i) = Px (0-i)
neg (Cm i) = Cm (0-i)

leq :: Mag u -> Mag u -> Bool
leq (Px a) (Px b) = a<=b
leq (Cm a) (Cm b) = a<=b

plus :: Mag u -> Mag u -> Mag u
plus (Px a) (Px b) = Px (a+b)
plus (Cm a) (Cm b) = Cm (a+b)

minus :: Mag u -> Mag u -> Mag u
minus (Px a) (Px b) = Px (a-b)
minus (Cm a) (Cm b) = Cm (a-b)

times :: Mag u -> Mag u -> Mag u
times (Px a) (Px b) = Px (a*b)
times (Cm a) (Cm b) = Cm (a*b)

square a = times a a
between a b c = leq a b && leq b c

--------------------------------------------------------------------------------
-- intensional version

data RegExp u
        = Univ
        | Empty
        | Circle (Mag u)
        | Rect (Mag u) (Mag u)
        | Union (RegExp u) (RegExp u)
        | Inter (RegExp u) (RegExp u)
        | Trans (Mag u, Mag u) (RegExp u)
        | forall v. Convert (CoordTrans v u) (RegExp v)


data CoordTrans :: Unit ~> Unit ~> *0 where
   CM2PX :: CoordTrans Centimeter Pixel
   PX2CM :: CoordTrans Pixel Centimeter


-- for such a trivial domain, we can make certain assumptions
twoPoint :: CoordTrans a b -> CoordTrans b c -> Equal a c
twoPoint CM2PX PX2CM = Eq
twoPoint PX2CM CM2PX = Eq

opp :: CoordTrans a b -> CoordTrans b a
opp CM2PX = PX2CM
opp PX2CM = CM2PX

eval :: RegExp u -> Region u
eval Univ                       = univ
eval Empty                      = empty
eval (Circle r)                 = circle r
eval (Rect w h)                 = rect w h
eval (Union a b)                = union (eval a) (eval b)
eval (Inter a b)                = intersect (eval a) (eval b)
eval (Trans xy r)               = trans xy (eval r)
eval (Convert trans r)  = convert (evalTrans trans) (eval r)

evalTrans :: CoordTrans u v -> Mag v -> Mag u
evalTrans CM2PX = pxTOcm
evalTrans PX2CM = cmTOpx


-- normalize r  puts r into a normal form.  
-- It does so by replacing all its constructors with
-- "smart" constructors in a bottom-up fashion.
normalize :: RegExp u -> RegExp u
normalize (Union a b)   = mkUnion (normalize a) (normalize b)
normalize (Inter a b)   = mkInter (normalize a) (normalize b)
normalize (Trans xy r)  = mkTrans xy (normalize r)
normalize (Convert t r) = mkConvert t (normalize r)
normalize t             = t

mkUnion :: RegExp u -> RegExp u -> RegExp u
mkUnion a     Univ        = Univ
mkUnion Univ  b           = Univ
mkUnion a     Empty       = a
mkUnion Empty b           = b
mkUnion a     (Inter x y) = Inter (mkUnion a x) (mkUnion a y)
mkUnion a     b           = Union a b

mkInter :: RegExp u -> RegExp u -> RegExp u
mkInter Univ  b     = b
mkInter a     Univ  = a
mkInter Empty b     = Empty
mkInter a     Empty = Empty
mkInter a     b     = Inter a b

mkTrans :: (Mag u,Mag u) -> RegExp u -> RegExp u
mkTrans (x,y) (Trans (u,v) r) = Trans (plus x u, plus y v) r
mkTrans xy    (Union a b)     = Union (mkTrans xy a) (mkTrans xy b)
mkTrans xy    (Inter a b)     = Inter (mkTrans xy a) (mkTrans xy b)
mkTrans xy    Univ            = Univ
mkTrans xy    Empty           = Empty
mkTrans xy    r               = Trans xy r

mkConvert :: CoordTrans u v -> RegExp u -> RegExp v
mkConvert t (Convert t' r)  = case twoPoint t' t of Eq -> r
mkConvert t (Univ)          = Univ
mkConvert t (Empty)         = Empty
mkConvert t (Union a b)     = Union (mkConvert t a) (mkConvert t b)
mkConvert t (Inter a b)     = Inter (mkConvert t a) (mkConvert t b)
mkConvert t (Circle rad)    = Circle (upd t rad)
mkConvert t (Rect w h)      = Rect (upd t w) (upd t h)
mkConvert t (Trans (dx,dy) r)= Trans (upd t dx,upd t dy) 
                                                (mkConvert t r)

upd t a = evalTrans (opp t) a

bigUnion :: [RegExp u] -> RegExp u
bigUnion = foldr Union Empty

bigInter :: [RegExp u] -> RegExp u
bigInter = foldr Inter Univ

--------------------------------------------------------------------------------
-- staged version

data CodeMag :: Unit ~> *0 where
   CodePx :: (Code Int) -> CodeMag Pixel
   CodeCm :: (Code Int) -> CodeMag Centimeter

liftMag :: Mag u -> CodeMag u
liftMag (Px i) = CodePx (lift i) 
liftMag (Cm i) = CodeCm (lift i)

pxTOcmS :: CodeMag Pixel -> CodeMag Centimeter
pxTOcmS (CodePx i) = CodeCm [| rem $i $(lift scale) |]

cmTOpxS :: CodeMag Centimeter -> CodeMag Pixel
cmTOpxS (CodeCm i) = CodePx [| $i * $(lift scale) |]

-- overloaded operators on Magnitudes. leave these out in the writeup
leqS :: CodeMag u -> CodeMag u -> Code Bool
leqS (CodePx a) (CodePx b) = [| $a <= $b |]
leqS (CodeCm a) (CodeCm b) = [| $a <= $b |]

plusS :: CodeMag u -> CodeMag u -> CodeMag u
plusS (CodePx a) (CodePx b) = CodePx [| $a + $b |]
plusS (CodeCm a) (CodeCm b) = CodeCm [| $a + $b |]

minusS :: CodeMag u -> Mag u -> CodeMag u
minusS (CodePx a) (Px 0) = CodePx a
minusS (CodePx a) (Px b) = if b < 0
                                then CodePx [| $a + $(lift (0-b)) |]
                                else CodePx [| $a - $(lift b) |]
minusS (CodeCm a) (Cm 0) = CodeCm a
minusS (CodeCm a) (Cm b) = if b < 0
                                then CodeCm [| $a + $(lift (0-b)) |]
                                else CodeCm [| $a - $(lift b) |]

timesS :: CodeMag u -> CodeMag u -> CodeMag u
timesS (CodePx a) (CodePx b) = CodePx [| $a * $b |]
timesS (CodeCm a) (CodeCm b) = CodeCm [| $a * $b |]

squareS a = timesS a a
betweenS a b c = [| $(leqS a b) && $(leqS b c) |]

-- basic regions (staged)
circleS :: Mag u ->
        CodeMag u -> CodeMag u -> Code Bool
circleS r x y = leqS (plusS (squareS x) (squareS y)) (liftMag (square r))
circleS (Px r) (CodePx x) (CodePx y) = 
      [| (($x * $x) + ($y * $y)) <= $(lift (r*r)) |]

rectS :: Mag u -> Mag u ->
        (CodeMag u -> CodeMag u -> Code Bool)
rectS w h x y = 
        [| $(betweenS (liftMag (neg w)) (plusS x x) (liftMag h)) && 
           $(betweenS (liftMag (neg h)) (plusS y y) (liftMag h)) |]

univS :: CodeMag u -> CodeMag u -> Code Bool
univS x y = [| True |]

emptyS :: CodeMag u -> CodeMag u -> Code Bool
emptyS x y = [| False |]

-- region combinators (staged)
transS :: (Mag u,Mag u) ->
        (CodeMag u -> CodeMag u -> Code Bool) ->
        (CodeMag u -> CodeMag u -> Code Bool)
transS (a,b) r x y = r (minusS x a) (minusS y b)

convertS :: (CodeMag v -> CodeMag u) ->
        (CodeMag u -> CodeMag u -> Code Bool) ->
        (CodeMag v -> CodeMag v -> Code Bool)
convertS t r x y = r (t x) (t y)

intersectS ::
        (CodeMag u -> CodeMag u -> Code Bool) ->
        (CodeMag u -> CodeMag u -> Code Bool) ->
        (CodeMag u -> CodeMag u -> Code Bool)
intersectS r1 r2 x y = [| $(r1 x y) && $(r2 x y) |]

unionS ::
        (CodeMag u -> CodeMag u -> Code Bool) ->
        (CodeMag u -> CodeMag u -> Code Bool) ->
        (CodeMag u -> CodeMag u -> Code Bool)
unionS r1 r2 x y = [| $(r1 x y) || $(r2 x y) |]

evalT :: RegExp u -> CodeMag u -> CodeMag u -> Code Bool
evalT Univ x y = [| True |]
evalT Empty x y = [| False |]
evalT (Circle r) x y = 
   leqS (plusS (squareS x) (squareS y)) (liftMag (square r))
evalT (Rect w h) x y = 
   [| $(betweenS (liftMag (neg w)) (plusS x x) (liftMag h)) && 
      $(betweenS (liftMag (neg h)) (plusS y y) (liftMag h)) |]
evalT (Union r1 r2) x y = [| $(evalT r1 x y) || $(evalT r2 x y) |]
evalT (Inter r1 r2) x y = [| $(evalT r1 x y) && $(evalT r2 x y) |]
evalT (Trans (a,b) r) x y = (evalT r) (minusS x a) (minusS y b)
evalT (Convert t r) x y = (evalT r) (compTrans t x) (compTrans t y)

comp :: RegExp u -> CodeMag u -> CodeMag u -> Code Bool
comp Univ               = univS
comp Empty              = emptyS
comp (Circle r)         = circleS r
comp (Rect w h)         = rectS w h
comp (Union a b)        = unionS (comp a) (comp b)
comp (Inter a b)        = intersectS (comp a) (comp b)
comp (Trans xy r)       = transS xy (comp r)
comp (Convert trans r)  = convertS (compTrans trans) (comp r)

compTrans :: CoordTrans u v -> CodeMag v -> CodeMag u
compTrans CM2PX = pxTOcmS
compTrans PX2CM = cmTOpxS

makePt :: Int -> Int -> (Mag Centimeter,Mag Centimeter)
makePt x y = (Cm x, Cm y)

r1 = Convert CM2PX (Union (Circle (Cm 5)) (Rect (Cm 5) (Cm 1)))
r2 = Union (Union Univ (Rect (Px 5) (Px 5))) Empty
r3 = Convert CM2PX (Trans (makePt 3 3) (Trans (makePt 1 1) (Circle (Cm 1))))
r4 = Convert CM2PX (Convert PX2CM (Circle (Px 1)))
r5 = Convert CM2PX (bigUnion (map (Convert PX2CM) [r1,r2,r3,r4]))

replicate 0 x = []
replicate n x = x : replicate (n-1) x

spaceOut (d@(dx,dy)) xs = space (minus dx dx,minus dy dy) xs
  where
    space p []     = Empty
    space p (x:xs) = Union (Trans p x) (space (plusPair p d) xs)
    plusPair (x,y) (u,v) = (plus x u, plus y v)

c0 = Circle (Cm 1)
r6 = Convert CM2PX (
      Trans (Cm (0-2),Cm 0) (
       spaceOut (Cm 2, Cm 0) [c0,c0,c0] ))

f [] = Empty
f (x:xs) = Union x (Trans (Cm 2,Cm 0) (f xs))

r7 = Convert CM2PX
       (Trans (Cm (0-2),Cm 0)
       (f [c0,c0,c0]))

-- for comparing the effects of optimization on code
evalPlain r = [| \(Px a) (Px b) -> $(comp r   (CodePx [|a|]) (CodePx [|b|])) |]
evalOpt r = [| \(Px a) (Px b) -> $(comp (normalize r)(CodePx [|a|]) (CodePx [|b|])) |]
eval2 r = run (evalOpt r)

--------------------------------------------------------------------------------
-- generating postscript

data Cmd = forall u. Disk Pt SomeMag | Box Pt Pt | Screen | Translate Pt
data Pt = Pt SomeMag SomeMag
data SomeMag = forall u. SomeMag (Mag u)

showCmd :: Cmd -> [Char]
showCmd Screen = "fillscreen"
showCmd (Disk c r) = "newpath "++showPt c++" "++showSomeMag r++" circle fill\n"
showCmd (Box b t) = "newpath " ++ showPt b ++ " " ++ showPt t ++ " box fill\n"
showCmd (Translate dxy) = showPt dxy ++ " translate\n"

mkPt :: (Mag u,Mag u) -> Pt
mkPt (x,y) = Pt (SomeMag x) (SomeMag y)

showMag :: Mag u -> [Char]
showMag (Px i) = show i ++ " px"
showMag (Cm i) = show i ++ " cm"

origin :: Pt
origin = mkPt (Px 0, Px 0)

negPair (a,b) = (neg a, neg b)

showSomeMag (SomeMag len) = showMag len

showPt :: Pt -> [Char]
showPt (Pt l1 l2) = showSomeMag l1 ++ " " ++ showSomeMag l2


compile :: RegExp u -> [Cmd] -> [Cmd]
compile (Univ)        k = Screen : k
compile (Empty)       k = k
compile (Circle r)    k = Disk origin (SomeMag r) : k
compile (Rect w h)    k = box w h : k
compile (Convert t r) k = compile r k
compile (Trans dxy r) k = Translate (mkPt dxy)
                           : (compile r 
                               (Translate (mkPt (negPair dxy)) : k))
compile (Union r1 r2) k = compile r1 (compile r2 k)
compile (Inter r1 r2) k = error "can't compile Intersections yet"

box :: Mag u -> Mag u -> Cmd
box (Px x) (Px y) = Box (mkPt (Px bx,Px by)) (mkPt (Px tx,Px ty))
        where (bx,by) = (rem x 2, rem y 2)
              (tx,ty) = (x - bx, y - by)
box (Cm x) (Cm y) = Box (mkPt (Cm bx,Cm by)) (mkPt (Cm tx,Cm ty))
        where (bx,by) = (rem x 2, rem y 2)
              (tx,ty) = (x - bx, y - by)

--displayPS :: [Cmd] -> [Char]

go r = map showCmd (compile r [])


