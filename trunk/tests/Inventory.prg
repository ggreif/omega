
kind Inventory a = Empty | More (Inventory a) Nat deriving LeftList(i)

merge :: Inventory Nat ~> Inventory Nat ~> Inventory Nat
{merge []i i} = i
{merge [as; a]i []i} = [as; a]i
{merge [as; a]i [bs; b]i} = {arrange as bs a b a b}

-- arrange is a helper to merge
--
arrange :: Inventory Nat ~> Inventory Nat ~> Nat ~> Nat ~> Nat ~> Nat ~> Inventory Nat
{arrange i j 0t (1+b')t a b} = [{merge [i; a]i j}; b]i
{arrange i j (1+a')t 0t a b} = [{merge i [j; b]i}; a]i
{arrange i j (1+a')t (1+b')t a b} = {arrange i j a' b' a b}

