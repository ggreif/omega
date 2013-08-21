
kind Inventory a = Empty | More (Inventory a) a deriving LeftList(i)

-- define rules at the type level (merging of inventories)
--
merge :: Inventory Nat ~> Inventory Nat ~> Inventory Nat
{merge []i i} = i
{merge [as; a]i []i} = [as; a]i
{merge [as; a]i [bs; b]i} = {arrange a b [as; a]i [bs; b]i}

-- arrange is a helper to merge, finds out which natural must come at end
--
arrange :: Nat ~> Nat ~> Inventory Nat ~> Inventory Nat ~> Inventory Nat
{arrange 0t (1+r)t [i; a]i [j; b]i} = [{merge [i; a]i j}; b]i
{arrange (1+l)t 0t [i; a]i [j; b]i} = [{merge i [j; b]i}; a]i
{arrange (1+l)t (1+r)t i j} = {arrange l r i j}

