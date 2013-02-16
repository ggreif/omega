-- Modeling Opetopes

import "../tests/NatList.prg"

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

