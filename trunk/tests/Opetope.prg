-- Modeling Opetopes
-- here is Eric's editor: http://sma.epfl.ch/~finster/opetope/opetope.html
--
-- Note: Kock et al. use a similar scheme, where
--          - dots    <-->   lines
--          - spheres <-->   dots
--          - lines disappear
--          -                spheres appear

-- Note: In Eric's new work (at IAS) there are no
--       dots any more, instead he uses 'external cards', so
--          - (external) cards   <-->  lines
--          - space between stacked cards <--> external cards
--          - lines disappear
--          -                (regular) cards appear

import "../src/LangPrelude.prg" (maybeM)
import "../tests/Nat.prg"

##bounds backchain 10

-- GLOBAL TODOs
----------------

-- Naming: Seems essential for identifying things Hor(Name), Ver(Tree)
--         Name can be Label, then Niches (= sequences of opetope names).
--         the latter arise from the composition rule.
--         Note: don't store names in Stacks, that kills alpha
--               conversion. Instead names should be pushed into nodes
--               'singleton style' from outside: (node :: Tree (Hor `g))

-- Morphisms: given an opetope and a pointer to one of its cards
--            extract the opetope of that face (do we need a label
--            space to reliably find it?). This must be a type
--            function, with an algorithm accompanying it to extract
--            the face proper.

-- Composition: grafting of trees to external cards, but only if the
--              morphisms (faces) match. lower-dim stuff is unaffected.

-- Swapping: given a proof of equality between two niches, provide an
--           operation to swap them, replacing old faces by new ones,
--           FGL-style (functional graph library), just note that
--           certain morphisms are gone, others appeared.

-- References: a disciplined way of saying "I am an identical node to that guy",
--             by corollary these always obtain the same names.
--             a topologist would say 'surgery' (http://en.wikipedia.org/wiki/Surgery_theory)
--             We get a new Tree flavour, Ref, at least one up, followed by
--             naturals to index a node in a subtree.
--             At this point we are doing algebraic topology, and dealing with
--             closed manifolds, so that we can do homology etc. on them.
--             In logic this corresponds to relations, satisfiability.

-- Quoting: So far we have only dealt with data, i.e. quoted (inert) syntax.
--          we need a way to convert this syntax to code (e.g. at some stage),
--          to obtain semantics. We can have the usual splicing game.
--          Lisp does this with sexprs and macros.
--          The code needs then be executed (run, decreasing stage), when
--          it becomes active, and we can observe the manifestation of its
--          semantics. The reduction system could go along the lines of the
--          (typed) LambdaGraph.

-- NbE: I fully believe we can use this technique to reduce opetopic terms
--      to normal form. ('many syntax', 'one semantics' adjunction:
--                       http://www.logicmatters.net/resources/pdfs/Galois.pdf)




-- TODO: these three must be LeftLists
--
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
  Fork :: treelike head -> Tree' tail -> Tree' [head; tail]tr
  Done :: Tree' []tr
 deriving syntax (ar) List(Done, Fork) Unit(In) -- "arbre"
-- http://www.papoulipoesique.com/wp-content/uploads/2013/06/arbre.jpg

-- define a proposition for subtrees
-- to be checked: TakeHead must ensure that all the node is consumed

prop Subtree :: Tree d ~> Tree e ~> * where
  UnitSub :: Subtree ()tr tr
  BothNil :: Subtree []tr []tr
  TakeHead :: Subtree head head' -> Subtree tail tail' -> Subtree [head; tail]tr [head'; tail']tr

-- TODO: separate the notions of Niche / Frame / Cell
kind Volume = FramedHollow | FilledCell
kind Diagram = Closed Volume | OpenNiche
-- should be a parameter to Stack

-- now we can stack cards (these are zooms in Kock et al. parlance)

data Stack :: Tree d ~> Tree e ~> * where
  Corolla :: Corolla tr => Tree' tr -> Stack tr ()tr

  -- TODO: needed?
  --Expand :: (Subtree consumed tr, {nodeValence consumed} `Equal` {nodeValence tr}) => Stack consumed prod -> Stack tr prod

  -- add another target face to a web
  Target :: ({nodes tr} `Equal` {nodeValence out}) => Stack tr out -> Stack tr out

  -- the following three grab a node (and possibly its offsprings) and incorporate it into a single card
  NodeDone :: Stack []tr [()tr]tr
  Pick :: {- EntireNode => -} Stack head prodhead -> Stack tail prodtail -> Stack [head; tail]tr [prodhead; prodtail]tr
  Exclude :: {- EntireNode => -} Stack tail prod -> Stack [()tr; tail]tr prod
  -- TODO: maybe just specify a subtree (Tree') and that's it

  On :: (Subtree tr' tr, Pointers 1t at out) => Stack tr' out' -> Stack tr out -> Tree' at -> Stack tr {graft out' at out}

  -- building niches (pasting diagrams)
  -- TODO: these must produce a composite labelled Hor
  NicheDone :: Stack ()tr []tr
  Niche :: Stack tr out -> Stack tr [out]tr
  Also :: Pointers 1t at tr
       => Tree' at -> Stack tr' out' -> Stack tr out -> Stack {extgraft tr' at tr} [out'; out]tr

  -- put a frame around a niche
  Frame :: (Corolla out, {nodes tr}  `Equal` {nodeValence out}) => Stack tr out -> Stack tr out

 deriving syntax(z) Record(NicheDone, Also) Item(Target)

stop = ({}z)z

-- this is bogus, just make it compile again...
up :: Reference tr => Stack ()tr tr -> Stack ()tr [tr]tr
up inner = ({()ar=inner}z)z

-- it remains to define corollas

-- TODO: one could say {nodes tr} == 1
prop Corolla :: Tree d ~> * where
  None' :: Corolla []tr
  One' :: Corolla tail -> Corolla [()tr; tail]tr

--  o   --->  |
--  |         |

lolliCell :: Stack []tr ()tr
lolliCell = Corolla Done

--  |         |
--  o   --->  |
--  |         |

dolliCell :: Stack [()tr]tr ()tr
dolliCell = Corolla $ Fork In Done

--              |
--  [o]   --->  o
--   |          |

lolliFrame :: Stack []tr [()tr]tr
lolliFrame = Target NodeDone

--   |          |
--  [o]   --->  o
--   |          |

dolliFrame :: Stack [()tr]tr [()tr]tr
dolliFrame = Target (Exclude NodeDone)

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
crossed = stop

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
drossed = up stop


-- ################################
-- ############  Niches ###########
-- ################################

--  |          +
--  |          |

-- this is a niche, but assume to be a frame
niche0 :: Stack ()tr []tr
niche0 = {}z

--  |           |
-- [|]          +
--  |           |

-- this is a niche, but assume to be a frame
niche1 :: Stack ()tr [[]tr]tr
niche1 = {()ar=stop; {}z}z

--  |         o   o
-- [|]  --->   \ /
-- [|]          +
--  |           |

-- this is a niche, but assume to be a frame
niche2 :: Stack ()tr [[]tr, []tr]tr
niche2 = {()ar=stop; niche1}z

--                |
--  |         o   o
-- [o]  --->   \ /
-- [|]          +
--  |           |


niche10 :: Stack [()tr]tr [[()tr]tr, []tr]tr
niche10 = {()ar=Exclude NodeDone; Niche stop}z


-- ################################
-- ############  Frames ###########
-- ################################

--   |              |
--  /|\         o   o
-- |[o]|  --->   \ /
-- |[|]|          o
--  \|/           |
--   |

cyclops :: Stack [()tr]tr [[()tr]tr, []tr]tr
cyclops = (niche10)z


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

-- counting nodes in a tree

nodes :: Tree d ~> Nat
{nodes ()tr} = t
{nodes []tr} = 1t
{nodes [head; tail]tr} = {plus {nodes head} {nodes tail}}

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

-- extgraft: extend and graft
--
extgraft :: Tree what ~> Tree wher ~> Tree tree ~> Tree tree'
{extgraft what ()tr ()tr} = what
{extgraft what []tr ()tr} = ()tr
{extgraft what [head; tail]tr ()tr} = {extgrafthor what [head; tail]tr}
{extgraft what []tr []tr} = []tr
{extgraft what []tr [head; tail]tr} = [head; tail]tr
{extgraft what [head'; tail']tr [head; tail]tr} = [{extgraft what head' head}; {extgraft what tail' tail}]tr

-- helper:
extgrafthor :: Tree what ~> Tree Hor ~> Tree Hor
{extgrafthor what []tr} = []tr
{extgrafthor what [head; tail]tr} = [{extgraft what head ()tr}; {extgrafthor what tail}]tr


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


prop Reference :: Tree Hor ~> * where
  Stop :: Reference []tr
  Up :: Reference tr -> Reference [tr]tr
 deriving Nat(d) -- de Bruijn index

prop Teleport :: Tree Hor ~> * where
  Gate :: Teleport [()tr]tr
  Tele :: Teleport tr -> Teleport [tr]tr
 deriving Nat(sk) -- skips

{-

0
|   |
1   L  (lambda node)
|   |
2   1  (how many skips)
 \ /
  o
  |
  B  (binds here)
  |

Encodes \x.xx

-}

r2 = 2d
t1 = 1sk

lamX_XX = addBinder $ [r2, t1]ar

prop BindsUp :: Nat ~> Tree Hor ~> * where
  LastSkip :: BindsUp 1t [()tr]tr
  MoreSkip :: Teleport tr -> BindsUp n tr -> BindsUp (1+n)t [tr]tr
  -- prove Application node
  HeadBindsUp :: Nat' n -> BindsUp (1+n)t head -> BindsUp n [head; tail]tr
  TailBindsUp :: BindsUp n [head; tail]tr -> BindsUp n [nonempty, head; tail]tr

-- TODO: make sure that something teleports here
addBinder :: BindsUp 1t tr => Tree' tr -> Tree' [tr]tr
addBinder term = [term]ar

testB :: BindsUp 0t [[[[]tr]tr]tr,[()tr]tr]tr -> Tree' [[[[]tr]tr]tr,[()tr]tr]tr
testB ev = [r2, 0sk]ar
testB' = testB (TailBindsUp (HeadBindsUp 0v (LastSkip)))

testC :: BindsUp 0t [[[[[]tr]tr]tr,[[()tr]tr]tr]tr]tr -> Tree' [[[[[]tr]tr]tr,[[()tr]tr]tr]tr]tr
testC ev = lamX_XX
testC' = testC (HeadBindsUp 0v (TailBindsUp (HeadBindsUp 1v (MoreSkip 0sk LastSkip))))


--TODO: prop Lambda :: Tree Hor ~> * where

{-
The slogan is: binder nodes do not count as result nodes:
 - just consider the next node upstream
 - incoming (external) cards, when identified to a binder do not count as inputs to application
 - incoming (external) cards, when identified to an (iterated) application become pattern matching (sigma).

In the end all identifications have a semantics (hopefully!), when the counting rules are ensured.

-}


-- Now some fun stuff

data LC :: Shape ~> (k ~> *) ~> * where
  Var :: tf a -> LC (Rf a') tf
  App :: LC fsh tf -> LC ash tf -> LC (fsh `Ap` ash) tf
  Lam :: tf a -> LC sh tf -> LC (Lm sh) tf
  LetRec :: tf a -> LC ish tf -> LC esh tf -> LC ((Lm esh) `Ap` ish) tf
 deriving syntax (lc) Applicative(Var, App, Lam, LetRec)

alamX_XX = (\x->x x)lc

kind Dict key value = Dempty | Dextend (Dict key value) key value deriving LeftRecord(dict)

-- Contexts map keys to some value
--
data Context :: (key ~> *) ~> (value ~> *) ~> Dict key value ~> * where
  Empty :: Context key value {}dict
  Extend :: Context key value dict -> key k -> value v -> Context key value {dict; k = v}dict
 deriving LeftRecord(ctx)

-- DeBrujn levels as keys
--
dictSize :: Dict key value ~> Nat
{dictSize {}dict} = 0t
{dictSize {pre; k = v}dict} = (1+{dictSize pre})t

data DeBrujnContext :: (value ~> *) ~> Dict Nat value ~> * where
  DeBrujnEmpty :: DeBrujnContext value {}dict
  DeBrujnExtend :: DeBrujnContext value dict -> value v -> DeBrujnContext value {dict; {dictSize dict} = v}dict
 deriving LeftList(dtx)


getDeBruijnIndex :: Dict key value ~> value ~> Nat ~> Nat
{getDeBruijnIndex {pre; k = v}dict v acc} = acc
{getDeBruijnIndex {pre; k = v'}dict v acc} = {getDeBruijnIndex pre v (1+acc)t}

lookUpDeBruijn :: DeBrujnContext Label dict -> Label l -> Nat' acc -> Maybe (Nat' {getDeBruijnIndex dict l acc})
lookUpDeBruijn []dtx _ _ = Nothing
lookUpDeBruijn [pre; known]dtx lab acc = case sameLabel known lab of
                                         R _ -> lookUpDeBruijn pre lab (1+acc)t
                                         L Eq -> Just acc

monad maybeM

toDeBruijn :: DeBrujnContext Label dict -> LC sh Label -> Maybe (LC sh Nat')
toDeBruijn ctx (Var a) = do idx <- lookUpDeBruijn ctx a 0t
                            return $ Var idx
toDeBruijn ctx (Lam l a) = do a' <- toDeBruijn [ctx; l]dtx a
                              return $ Lam 0t a'
toDeBruijn ctx (App f a) = do f' <- toDeBruijn ctx f
                              a' <- toDeBruijn ctx a
                              return $ App f' a'

-- Let :: tf a -> LC tf -> LC tf -> LC tf -- not needed!
pattern Let n v exp = App (Lam n exp) v

-- fun with church encoding

true = (\t->\f->t)lc
--false = (\t f->f)lc -- BUG!
false = (\t->\f->f)lc

-- church 'if'
chif = (\v->\iftrue->\iffalse->v iftrue iffalse)lc

chtest = (chif true false true)lc -- will not do what you expect
--chtest' = ($chif $true $false $true)lc -- not ready yet!

chtest'' = (let { true = \t->\f->t
                ; false = \t->\f->f
                ; chif = \v->\iftrue->\iffalse -> v iftrue iffalse
                }
            in chif true false true)lc -- this still does not work :-(

letrecToLet :: LC sh k -> LC sh k
letrecToLet (App f a) = App (letrecToLet f) (letrecToLet a)
letrecToLet (v@Var _) = v
letrecToLet (l@Lam _ _) = l
letrecToLet (LetRec n v e) = App (Lam n e) v -- Let n v e -- Omega pattern bug???

l2l = letrecToLet (let a = a in a)lc

-- shapes

kind Shape = Lm Shape | Ap Shape Shape | Rf Nat

--- ####### LC should be (primarily) parametrized in shape

data Shape' :: Shape ~> * where
  Ref :: Nat' n -> Shape' (Rf n)
  Lm :: Shape' inner -> Shape' (Lm inner)
  --Lm :: Shape' inner -> Shape' (Lm inner)

shape :: LC sh Nat' -> LC sh Shape'
shape (Var n) = Var (Ref n)
--shape (Lam n e) = Lam (Lm $ shape' e) $ shape e
shape (Lam n e) = Lam (Lm $ undefined) $ shape e

--shape' :: LC Nat' -> Shape' sh
--shape' (Var n) = Ref n


{-
data Shape :: *1 where
  Lm :: Shape ~> Shape
  Ap :: Shape ~> Shape ~> Shape
  Rf :: 
-}

data Dictionary :: Dict a b ~> * where
  Funny :: Dictionary {}dict

context :: DeBrujnContext Nat' dict -> LC sh Nat' -> LC sh Dictionary
context ctx (Var n) = Var undefined

-- abstractly interpret
-- this should be parameterized by a monad!

--interp :: Monad m -> LC (context tr) -> m (LC (context tr))