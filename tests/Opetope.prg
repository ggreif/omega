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

import "../tests/NatList.prg"

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
  BothUnit :: Subtree ()tr ()tr
  BothNil :: Subtree []tr []tr
  TakeHead :: Subtree head head' -> Subtree tail tail' -> Subtree [head; tail]tr [head'; tail']tr
  SkipHead :: Subtree tail tail' -> Subtree [head; tail]tr [head'; tail']tr

-- now we can stack cards (these are zooms in Kock et al. parlance)

data Stack :: Tree ~> Tree ~> * where
  Empty :: Corolla tr => Tree' tr -> Stack tr ()tr
  SubDone :: Stack ()tr []tr
  Subdivision :: Stack ()tr sub -> Stack tr rest -> Stack tr [sub; rest]tr
  Encompass :: Subtree consumed tr => Stack consumed prod -> Stack tr prod
  -- the following three grab a node
  NodeDone :: Stack []tr []tr
  Pick :: {- EntireNode => -} Stack head prodhead -> Stack tail prodtail -> Stack [head, tail]tr [prodhead, prodtail]tr
  Exclude :: {- EntireNode => -} Stack tail prod -> Stack [head, tail]tr prod

-- remains to define corollas

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

--    |           o   |
-- | [o] |  --->   \ /
-- | [|] |          o
--    |             |

--cyclops :: Stack [()tr]tr [[]tr, ()tr]tr
--cyclops = Subdivision SubDone (Exclude NodeDone)

--- OLD IMPLEMENTATION FOLLOWS

-- Node Types

kind NodeType = Regular | Universal

-- Node Labels (parametrized by dimension?)

data NodeLabel = Named (Label n)
               | Comp NodeLabel NodeLabel

-- Node: named faces as inputs and an output (face)


-- Consuming some twig

data Eat :: Twig ~> * where
  NoDot :: Eat None  -- do not extend till next sprouting point
  Sub :: Eat (Sprout l)

-- A connected deck of cards

data Deck :: Twig ~> Twig ~> * where
  Air :: Deck t None
  Card :: Eat t -> Deck subt out -> Deck t (Sprout [out]w)


-- A forest: trees in each dimension up to n
--   o when it ends in a corolla then it is a cell (n-dimensional)
--   

--data Forest


-- Idea: each tree must have two type parameters
--       o left: set of nodes from dim (n - 1) is our (tree of) lines
--       o right: my set of nodes is the tree I push to dim n + 1

-- HAH! we have a thrist!

-- trees live at the type level

-- have these forms
--      O  |
--   o  |  o
--      o

--         |
-- List of o starts at O

data List :: *1 where
  No :: List
  Ext :: List ~> Twig ~> List
 deriving LeftList(w)

data Twig :: *1 where
  None :: Twig
  Sprout :: List ~> Twig

-- an Opetope is a LeftThrist of Decks

-- Dimension Zero is always:

dim0 = Card NoDot Air

dim1 = Card Sub Air

upto1 = [dim0, dim1]lt

