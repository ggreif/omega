-- some infrastructure

kind Invariant = Pair a b deriving Pair(ip)

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
data Sig :: Signature ~> * where
  A :: Sig A
  B :: Sig B
  C :: Sig C

-- elementary transitions
--
data Transition :: Invariant ~> Invariant ~> * where
  -- message primitives
  Send :: Sig s' -> Transition (t, NotFlying, s)ip (t, Flying, s)ip
  Received :: Sig s -> Transition (t, h, s)ip (t, h, s')ip
  -- timer primitives
  StartTimer :: Int -> Transition (Stopped, f, s)ip (Running, f, s)ip
  StopTimer :: Transition (Running, f, s)ip (Stopped, f, s)ip
  Expired :: Transition (Running, f, s)ip (Stopped, f, s)ip
  -- landing
  Land :: statelike t h s -> Transition (t, h, s)ip (t, h, s)ip
  -- building longer transition arrows
  Compose :: Transition (t, f, s)ip (t', f', s')ip -> Transition (t', f', s')ip (t'', f'', s'')ip
          -> Transition (t, f, s)ip (t'', f'', s'')ip


t1 = (Send B) `Compose` (StartTimer 4) `Compose` (Land StateA')