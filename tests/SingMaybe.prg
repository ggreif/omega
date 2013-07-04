

data Mayb :: a ~> *2 where
  Noth :: Mayb a
  Jus :: a ~> Mayb a

data Mayb1 :: Mayb a ~> *1 where
  Noth1 :: Mayb1 Noth
  Jus1 :: a ~> Mayb1 (Jus a)

data Mayb2 :: Mayb1 a ~> *0 where
  Noth2 :: Mayb2 Noth1
  Jus2 :: a -> Mayb2 (Jus1 a)

{-

It is strange that Omega adds level polymorphism
for the upper two. Witnessed by this dialogue:

prompt> :k Mayb
Mayb :: level b . forall (a::*(3+b)).a ~> *2

prompt> :k Mayb1
Mayb1 :: level b . forall (a::*(2+b)).Mayb a ~> *1

prompt> :k Mayb2
Mayb2 :: forall (a::Mayb *1).Mayb1 a ~> *0

prompt> :t Jus1 4
Not in scope: Jus1

prompt> :t Jus2 4
Jus2 4 :: Mayb2 (Jus1 Int)

prompt> :k Mayb2 (Jus1 Int)
Mayb2 (Jus1 Int) :: *0  = Mayb2 (Jus1 Int)

prompt> :k Jus1 Int        
Jus1 Int :: Mayb1 (Jus *0)  = Jus1 Int

prompt> :k Jus *0  
Jus *0 :: Mayb *1  = Jus *0

prompt> :k Jus *1
Jus *1 :: Mayb *2  = Jus *1

prompt> :k Jus *2
Jus *2 :: Mayb *3  = Jus *2

prompt> :k Jus
Jus :: level b . forall (a::*(3+b)) (c::a::*(3+b)).c ~> Mayb c

-}