-- -*-Haskell-*-

exclude :: Tag ~> Row Tag * ~> Row Tag *
{exclude o {}r} = {}r
{exclude a {a=v; r}r} = {exclude a r}
{exclude b {a=v; r}r} = {a=v; {exclude b r}}r

-- carrying dynamic evidence that no tag is occurring twice
-- of course in a real world we want a pair with payload
--
data SingleLabel' :: Row Tag * ~> * where
  None' :: SingleLabel' {}r
  More' ::  Label l -> Equal {exclude l rest} rest -> SingleLabel' rest -> SingleLabel' {l=t;rest}r
 deriving Record(sl)

t100 :: SingleLabel' {`a=a}r
t100 = {`a=Eq}sl

##test "duplicate label"
  t101 = {`a=Eq, `a=Eq}sl

t102 = {`a=Eq, `b=Eq}sl


reass t = case t of { {a=v;b}sl -> {a=v;b}sl }

##test "duplicate label, deeper"
  t103 = {`a=Eq, `b=Eq, `a=Int}sl

-- the below works but needs :bounds narrow upped
{-
t104 = {`a=Eq, `b=Eq, `c=Eq}sl

t105 = reass t104
-}
