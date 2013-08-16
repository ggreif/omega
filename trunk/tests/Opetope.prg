-- Modeling Opetopes
-- here is Eric's editor: http://sma.epfl.ch/~finster/opetope/opetope.html
--
-- Note: Kock et al. use a similar scheme, where
--          - dots    <-->   lines
--          - spheres <-->   dots
--          - lines disappear
--          -                spheres appear

-- Note: In Eric's new work (at IAS) there are no
--       dots any more, instead he uses 'output cards', so
--          - (output) cards   <-->  lines
--          - space between stacked cards <--> output cards
--          - lines disappear
--          -                (regular) cards appear

import "../tests/Nat.prg"

kind Trees = NoTree | Pre (Tree d) Trees deriving syntax (ts) List(NoTree, Pre)

data ZoomCompley :: Tree e ~> Tree f ~> * where
  Nily :: ZoomCompley a a
  Consy :: Stack a b -> ZoomCompley b c -> ZoomCompley a c
 deriving List(cply)

data ZoomComplex :: Trees ~> * where
  Nilx :: ZoomComplex [()tr]ts
  Endx :: Stack a b -> ZoomComplex [a, b]ts
  Consx :: Stack a b -> ZoomComplex [b; c]ts -> ZoomComplex [a, b; c]ts
 deriving syntax (cplx) List(Nilx, Consx) Item(Endx)

data Dir :: *2 where
  Hor :: Dir
  Ver :: Dir

-- define the Tree kind, a rose tree
-- note: we may need a two-level kind, since we need to track disjointness
--       of subtrees
-- todo: later we may want to have a label kind parameter too

data Tree :: Dir ~> *1 where
  Unit :: Tree Ver
  Ni :: Tree Hor
  Fork :: Tree d ~> Tree Hor ~> Tree Hor
 deriving syntax (tr) List(Ni, Fork) Unit(Unit)

-- make it singleton

data Tree' :: Tree d ~> * where
  In :: Tree' ()tr
  Fork :: Tree' head -> Tree' tail -> Tree' [head; tail]tr
  Done :: Tree' []tr
 deriving syntax (ar) List(Done, Fork) Unit(In) -- "arbre"
-- http://www.papoulipoesique.com/wp-content/uploads/2013/06/arbre.jpg

-- define a proposition for subtrees
-- to be checked: TakeHead must ensure that all the node is consumed

prop Subtree :: Tree d ~> Tree e ~> * where
  UnitSub :: Subtree ()tr tr
  BothNil :: Subtree []tr []tr
  TakeHead :: Subtree head head' -> Subtree tail tail' -> Subtree [head; tail]tr [head'; tail']tr

-- now we can stack cards (these are zooms in Kock et al. parlance)

data Stack :: Tree d ~> Tree e ~> * where
  Empty :: Corolla tr => Tree' tr -> Stack tr ()tr
  SubDone :: Stack ()tr []tr
  SubCont :: Stack ()tr tr -> Stack ()tr [tr]tr
  --Subdivision :: Stack ()tr sub -> Stack tr rest -> Stack tr [sub; rest]tr
  Encompass :: Subtree consumed tr => Stack consumed prod -> Stack tr prod
  -- the following three grab a node (and possibly its offsprings) and incorporate it into a single card
  NodeDone :: Stack []tr [()tr]tr
  Pick :: {- EntireNode => -} Stack head prodhead -> Stack tail prodtail -> Stack [head; tail]tr [prodhead; prodtail]tr
  Exclude :: {- EntireNode => -} Stack tail prod -> Stack [()tr; tail]tr prod
  -- we need a way to sequence cards
  -- MultiCard :: ??? Disjoint a b 0 => Subtree a -> Subtree b -> Stack tr a [proda, prodb]tr

  On :: (Subtree tr' tr, Pointers 1t at out) => Stack tr' out' -> Stack tr out -> Tree' at -> Stack tr {graft out' at out}

  -- building niches
  NicheDone :: Stack ()tr []tr
  Niche :: Stack tr out -> Stack tr [out]tr
  Also :: () -- (Pointers 1t at tr)
         => Tree' at -> Stack tr' out' -> Stack tr out -> Stack {extgraft tr' at tr} [out'; out]tr


-- it remains to define corollas

prop Corolla :: Tree d ~> * where
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

--   |
--  [|]   --->  o
--   |          |

crossed :: Stack ()tr []tr
crossed = SubDone

-- we can now join things
--
dolliForever = [dolliFrame; dolliForever]cply
nopetope = [crossed, lolliFrame; dolliForever]cply

-- back to unit as fast as possible...
--
stopetope = [crossed, lolliFrame, dolliCell]cply
neverstopetope = [crossed, lolliFrame, dolliCell; neverstopetope]cply
stopetope' = [crossed, lolliFrame; (dolliCell)cplx]cplx
stopetope'' = [crossed, lolliFrame, dolliCell]cplx

--   |          o
-- [[|]]  --->  |
--   |          o
--   |          |

drossed :: Stack ()tr [[]tr]tr
drossed = SubCont SubDone
-- drossed = (SubDone `On` NodeDone) In
-- Note: can we find a way to graft here? Then On would be feasible


-- ################################
-- ############  Niches ###########
-- ################################

--  |          +
--  |          |

-- this is a niche, but assume to be a frame
niche0 :: Stack ()tr []tr
niche0 = NicheDone

--  |           |
-- [|]          +
--  |           |

-- this is a niche, but assume to be a frame
niche1 :: Stack ()tr [[]tr]tr
niche1 = Also ()ar SubDone NicheDone

--  |         o   o
-- [|]  --->   \ /
-- [|]          +
--  |           |

-- this is a niche, but assume to be a frame
niche2 :: Stack ()tr [[]tr, []tr]tr
niche2 = Also ()ar SubDone niche1

--                |
--  |         o   o
-- [o]  --->   \ /
-- [|]          +
--  |           |

niche10 :: Stack [()tr]tr [[()tr]tr, []tr]tr
--niche10 = Also ()ar SubDone $ Niche (Exclude NodeDone)
niche10 = Also ()ar (Exclude NodeDone) $ Niche SubDone

--                    |
--    |           o   o
-- | [o] |  --->   \ /
-- | [|] |          o
--    |             |

--cyclops :: Stack [()tr]tr [[]tr, ()tr]tr
--cyclops = Pick (Beside ()ar ()ar SubDone (Exclude NodeDone)) NodeDone



-- Stacking, Valence, Affine subtree, Substitute at an affine position

-- counting Units in a tree

valence :: Tree d ~> Nat
{valence []tr} = 0t
{valence [head; tail]tr} = {plus {valence head} {valence tail}}
{valence ()tr} = 1t

-- counting siblings of a tree

nodeValence :: Tree d ~> Nat
{nodeValence []tr} = 0t
{nodeValence [head; tail]tr} = (1+{nodeValence tail})t

-- nodeValenceAt: given a (multi)pointer, determine the node valences at those positions
--               WHERE     IN
nodeValenceAt :: Tree d ~> Tree e ~> Nat
{nodeValenceAt ()tr tree} = {nodeValence tree}
{nodeValenceAt []tr []tr} = 0t
{nodeValenceAt [head'; tail']tr [head; tail]tr} = {plus {nodeValenceAt head' head} {nodeValenceAt tail' tail}}

-- a pointer is a valence-1 subtree of a tree
-- it is used to mark a unit in a tree where substitution will occur
--
prop Pointers :: Nat ~> Tree d ~> Tree e ~> * where
  Finger :: Pointers 1t ()tr ()tr
  Finished :: Pointers 0t []tr []tr
  ThisWay :: Pointers 1t head' head -> Pointers n tail' tail -> Pointers (1+n)t [head'; tail']tr [head; tail]tr
  ElseWhere :: Pointers n tail' tail -> Pointers n [[]tr; tail']tr [head; tail]tr

-- http://en.wikipedia.org/wiki/Grafting
--
-- graft WHAT      WHERE     IN
graft :: Tree d ~> Tree e ~> Tree f ~> Tree f
{graft what ()tr ()tr} = what
{graft what []tr tr} = tr
{graft what [head'; tail']tr [head; tail]tr} = [{graft what head' head}; {graft what tail' tail}]tr


extgraft :: Tree what ~> Tree wher ~> Tree tree ~> Tree tree'
{extgraft what ()tr ()tr} = what
{extgraft what []tr ()tr} = ()tr
{extgraft what [head; tail]tr ()tr} = [{extgraft what head ()tr}; {extgraft what tail ()tr}]tr
{extgraft what []tr []tr} = []tr
{extgraft what []tr [head; tail]tr} = [head; tail]tr
{extgraft what [head'; tail']tr [head; tail]tr} = [{extgraft what head' head}; {extgraft what tail' tail}]tr

{- TODO? multiGraft :: Treelist -> where -> in -}

{- NOTE: we have an Omega bug here:

prompt> :norm {graft []tr ()tr ()tr}
Normalizes to:
  []tr

prompt> :kind []tr
[]tr :: Tree Hor  = []tr

prompt> :kind {graft []tr ()tr ()tr}
{graft []tr ()tr ()tr} :: Tree Ver  = {graft []tr ()tr ()tr}

... BUT: Hor /= Ver :-(
-}

-- substitution: replace a pointed node (of valence n) in a tree with an
-- other tree of (valence n) -- TODO


-- HERE IS A NICE RESEARCH QUESTION:
-- is it possible to "proof search" a Zoom?
-- i.e.
{-

class ZoomLike (int :: Tree) (out :: Tree) where
  zoom :: (Nodes int ~ Valence out) => Zoom int out

-}
