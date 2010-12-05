import "../src/LangPrelude.prg" (map)


filter p [] = []
filter p (x:xs) = if p x then x : filter p xs else filter p xs

concat :: [[a]] -> [a]
concat [] = []
concat (xs : xss) = xs ++ concat xss

data Desc :: *0 ~> *0 ~> *0 where
   Nil :: Desc tuple u
   Cons :: String -> (Rep t) -> (tuple -> t) -> (Desc tuple m) -> Desc tuple ((t,m))
   Branch :: (Desc a a) -> (Desc b b) -> Desc ((a,b)) ((a,b))


retrieve :: Rep b -> String -> Desc a c -> Maybe(a->b)
retrieve rep str (Branch m n) =
  case retrieve rep str m of
    Just g -> Just(\ (x,y)->(g x))
    Nothing -> case retrieve rep str n of
      Just g -> Just(\ (x,y)->(g y))
      Nothing -> Nothing
retrieve rep str (Cons s r f xs) =
  if (eqStr str s)
    then case match rep r of
           Just Eq -> Just f
           Nothing -> retrieve rep str xs
    else retrieve rep str xs
retrieve rep str Nil = Nothing
                          

data Rel t = MkRel (Desc t t) [ t ] String

select :: Rel a -> (a -> Bool) -> Rel a
select (MkRel d xs nm) p = MkRel d (filter p xs) nm

project :: Rel a -> (a -> b) -> (Desc a a -> Desc b b) -> Rel b
project (MkRel d xs nm) f g = MkRel (g d) (map f xs) ""

cross :: Rel a -> Rel b -> (a -> b -> Bool) -> ( a -> b -> c) -> Rel c
cross (MkRel d1 xs1 nm1) (MkRel d2 xs2 nm2) match combine = undefined
 -- MkRel ?? [ combine x y | x <- xs1, y <- xs2, match x y ] "?"

cross2 :: Rel a -> Rel b -> Rel (a,b)
cross2 (MkRel d1 xs1 nm1) (MkRel d2 xs2 nm2) = MkRel (Branch d1 d2) answer ""
  where answer = concat (map f xs1)
                  where f x = map g xs2
                               where g y = (x,y)
  

d0 = (Cons "Age" Int getAge Nil)
  where getAge  (nm,(ag,_)) = ag
  
d1 = Cons "Name" String getName d0
  where getName (nm,(ag,_)) = nm
       


r1 = MkRel d1 [a,b,c ] "People"
  where a = ("Tom",(23,()))
        b = ("Bill",(19,()))
        c = ("Mary",(29,()))

f :: Rel a -> Maybe[String]
f (MkRel d tups nm) = g tups d
  where g :: [t] -> Desc t a -> Maybe [String]
        g tups Nil = Nothing
        g tups (Cons "Name" String proj y) = Just(map proj tups)
        g tups (Cons _ _ _ y) = g tups y
        
h :: Desc a v -> Desc b u -> Maybe(a -> b -> Bool)
h Nil Nil = Just(\ x y -> True)
-- h (Cons a r f xs) (Cons b s g ys) =

----------------------------------------------------

data Rep :: *0 ~> *0 where
   Int :: Rep Int
   Char :: Rep Char
   Bool :: Rep Bool
   String :: Rep String
   List :: (Rep a) -> Rep ([a])
   


match :: Rep a -> Rep b -> Maybe(Equal a b)
match Int Int = Just Eq
match Char Char = Just Eq
match Bool Bool = Just Eq
match String String = Just Eq
match (List a) (List b) = 
  case match a b of
    Just Eq -> Just Eq
    Nothing -> Nothing
match _ _ = Nothing
