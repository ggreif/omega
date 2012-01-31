-- some infrastructure

kind Invariant = Pair a b deriving Pair(i)

data Check :: * where
  Connect :: State t h s -> Transition (t, h, s)i (t', h', s')i -> State t' h' s' -> Check

-- invariants
--
kind Timer = Running | Stopped
kind HandShake = NotFlying | Flying
kind Signature = A | B | C

-- our possible states
--
data State :: Timer ~> HandShake ~> Signature ~> * where
  StateA :: State Stopped NotFlying A
  StateA' :: State Running Flying A
  StateB :: State Stopped NotFlying B
  StateB' :: State Running Flying B
  StateC :: State Stopped NotFlying C
  StateC' :: State Running Flying C

-- coherency protocol
--
data Message :: Signature ~> * where
  TriggerToA :: String -> Message C
  TriggerToB :: Message A
  TriggerToC :: Bool -> Message B
  AckToA :: Message C
  AckToB :: Message A
  AckToC :: Message B

-- referring to signatures
--
--data Sig :: Signature ~> * where
--  A :: Sig A
--  B :: Sig B
--  C :: Sig C

-- elementary transitions
--
data Transition :: Invariant ~> Invariant ~> * where
  -- external spark
  Spark :: Transition (t, h, s)i (t, h, s)i
  -- message primitives
  Send :: signed s -> Transition (t, NotFlying, s)i (t, Flying, s)i
  Receive :: signed s -> Transition (t, h, s)i (t, h, s')i
  AssumeLost :: Transition (t, Flying, s)i (t, NotFlying, s)i
  -- timer primitives
  StartTimer :: Int -> Transition (Stopped, f, s)i (Running, f, s)i
  StopTimer :: Transition (Running, f, s)i (Stopped, f, s)i
  Expired :: Transition (Running, f, s)i (Stopped, f, s)i
  -- landing
  Land :: statelike t h s -> Transition (t, h, s)i (t, h, s)i
  -- building longer transition arrows
  Compose :: Transition (t, f, s)i (t', f', s')i -> Transition (t', f', s')i (t'', f'', s'')i
          -> Transition (t, f, s)i (t'', f'', s'')i
 deriving syntax(t) LeftPair(Compose)


t1 = Spark `Compose` Send TriggerToB `Compose` StartTimer 4 `Compose` Land StateA'
c1 = Connect StateA t1 StateA'
t1' = Receive TriggerToB `Compose` Send AckToB `Compose` StartTimer 1 `Compose` Land StateA'
c1' = Connect StateA t1' StateA'

t2 = Expired `Compose` AssumeLost `Compose` Send AckToB `Compose` StartTimer 1 `Compose` Land StateA'
c2 = Connect StateA' t2 StateA'
