-- Modeling Opetopes
-- here is Eric's editor: http://sma.epfl.ch/~finster/opetope/opetope.html
--
-- Note: Kock et al. use a similar scheme, where
--          - dots    <-->   lines
--          - spheres <-->   dots
--          - lines disappear
--          -                spheres appear

-- Note: In Eric's new work (at IAS) there are no
--       dots any more, instead he uses 'outout cards', so
--          - (output) cards   <-->  lines
--          - space between stacked cards <--> output cards
--          - lines disappear
--          -                (regular) cards appear

--import "../tests/NatList.prg"
import "../tests/Nat.prg"

-- list kind
--kind List = Ni | Co 

-- define the Tree kind, a rose tree
-- note: Ni may only appear in Fork second position (TODO: use GADT!)

kind Tree = Unit | Ni | Fork Tree Tree deriving syntax (tr) List(Ni, Fork) Unit(Unit)

-- make it singleton

data Tree' :: Tree ~> * where
  In :: Tree' ()tr
  Fork :: Tree' head -> Tree' tail -> Tree' [head; tail]tr
  Done :: Tree' []tr

-- define a proposition for subtrees
-- to be checked: TakeHead must ensure that all the node is consumed

prop Subtree :: Tree ~> Tree ~> * where
  UnitSub :: Subtree ()tr tr
  BothNil :: Subtree []tr []tr
  TakeHead :: Subtree head head' -> Subtree tail tail' -> Subtree [head; tail]tr [head'; tail']tr

-- now we can stack cards (these are zooms in Kock et al. parlance)

data Stack :: Tree ~> Tree ~> * where
  Empty :: Corolla tr => Tree' tr -> Stack tr ()tr
  SubDone :: Stack ()tr []tr
  Subdivision :: Stack ()tr sub -> Stack tr rest -> Stack tr [sub; rest]tr
  Encompass :: Subtree consumed tr => Stack consumed prod -> Stack tr prod
  -- the following three grab a node (and possibly its offsprings) and incorporate it into a single card
  -- [perhaps, note: there may be other cards stacked on this one]
  NodeDone :: Stack []tr [()tr]tr
  Pick :: {- EntireNode => -} Stack head prodhead -> Stack tail prodtail -> Stack [head; tail]tr [prodhead; prodtail]tr
  Exclude :: {- EntireNode => -} Stack tail prod -> Stack [()tr; tail]tr prod
  -- we need a way to sequence cards
  -- MultiCard :: ??? Disjoint a b 0 => Subtree a -> Subtree b -> Stack tr a [proda, prodb]tr

  On :: (Subtree tr' tr, Pointers 1t at out) => Stack tr' out' -> Stack tr out -> Tree' at -> Stack tr {substitute out' at out}

-- it remains to define corollas

prop Corolla :: Tree ~> * where
  None' :: Corolla []tr
  One' :: Corolla tail -> Corolla [()tr; tail]tr

--  o   --->  |
--  |         |

lolliCell :: Stack []tr ()tr
lolliCell = Empty Done

--  |         |
--  o   --->  |
--  |         |

dolliCell :: Stack [()tr]tr ()tr
dolliCell = Empty $ Fork In Done

--              |
--  [o]   --->  o
--   |          |

lolliFrame :: Stack []tr [()tr]tr
lolliFrame = Encompass NodeDone

--   |          |
--  [o]   --->  o
--   |          |

dolliFrame :: Stack [()tr]tr [()tr]tr
dolliFrame = Encompass (Exclude NodeDone)

--   |          |
--   |          o
-- [[o]]  --->  |
--   |          o
--   |          |

stacked :: Stack [()tr]tr [[()tr]tr]tr
stacked = (dolliFrame `On` dolliFrame) (In `Fork` Done)

--    |           o   |
-- | [o] |  --->   \ /
-- | [|] |          o
--    |             |

--cyclops :: Stack [()tr]tr [[]tr, ()tr]tr
--cyclops = Subdivision SubDone (Exclude NodeDone)



-- Stacking, Valence, Affine subtree, Substitute at an affine position

-- counting Units in a tree

valence :: Tree ~> Nat
{valence []tr} = 0t
{valence [head; tail]tr} = {plus {valence head} {valence tail}}
{valence ()tr} = 1t

-- counting siblings of a tree

nodeValence :: Tree ~> Nat
{nodeValence []tr} = 0t
{nodeValence [head; tail]tr} = (1+{nodeValence tail})t


-- a pointer is a valence-1 subtree of a tree
-- it is used to mark a unit in a tree where substitution will occur
--
prop Pointers :: Nat ~> Tree ~> Tree ~> * where
  Finger :: Pointers 1t ()tr ()tr
  Finished :: Pointers 0t []tr []tr
  ThisWay :: Pointers 1t head' head -> Pointers n tail' tail -> Pointers (1+n)t [head'; tail']tr [head; tail]tr
  ElseWhere :: Pointers n tail' tail -> Pointers n [[]tr; tail']tr [head; tail]tr

-- substitute WHAT    WHERE   IN
substitute :: Tree ~> Tree ~> Tree ~> Tree
{substitute what ()tr ()tr} = what
{substitute what []tr []tr} = []tr
{substitute what [head'; tail']tr [head; tail]tr} = [{substitute what head' head}; {substitute what tail' tail}]tr
