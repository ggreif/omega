
data Balance:: Nat ~> Nat ~> Nat ~> *0 where
  Same :: Balance n n n
  Less :: Balance n (S n) (S n)
  More :: Balance (S n) n (S n)

data Avl:: Nat ~> *0 where
  Tip:: Avl Z
  Node:: Balance i j k -> Avl i -> Int -> Avl j -> Avl (S k)

data AVL = forall h. AVL (Avl h)

insert :: Int -> AVL -> AVL
insert x (AVL t) = case ins x t of L t -> AVL t; R t -> AVL t

ins :: Int -> Avl n -> (Avl n + Avl (S n))
ins x Tip = R(Node Same Tip x Tip)
ins x (Node bal lc y rc)
  | x == y = L(Node bal lc y rc)
  | x < y  = case ins x lc of
               L lc -> L(Node bal lc y rc)
               R lc ->
                 case bal of
                   Same -> R(Node More lc y rc)
                   Less -> L(Node Same lc y rc)
                   More -> rotr lc y rc -- rebalance
  | x > y  = case ins x rc of
               L rc -> L(Node bal lc y rc)
               R rc -> 
                 case bal of
                   Same -> R(Node Less lc y rc)
                   More -> L(Node Same lc y rc)
                   Less -> rotl lc y rc -- rebalance

rotr :: Avl(S(S n)) -> Int -> Avl n -> (Avl(S(S n))+Avl(S(S(S n))))
rotr Tip u a = unreachable
rotr (Node Same b v c) u a = R(Node Less b v (Node More c u a))
rotr (Node More b v c) u a = L(Node Same b v (Node Same c u a))
rotr (Node Less b v Tip) u a = unreachable
rotr (Node Less b v (Node Same x m y)) u a = L(Node Same (Node Same b v x) m (Node Same y u a))
rotr (Node Less b v (Node Less x m y)) u a = L(Node Same (Node More b v x) m (Node Same y u a))
rotr (Node Less b v (Node More x m y)) u a = L(Node Same (Node Same b v x) m (Node Less y u a))

rotl :: Avl n -> Int -> Avl(S(S n)) -> (Avl(S(S n))+Avl(S(S(S n))))
rotl a u Tip = unreachable
rotl a u (Node Same b v c) = R(Node More (Node Less a u b) v c)
rotl a u (Node Less b v c) = L (Node Same (Node Same a u b) v c)
rotl a u (Node More Tip v c) = unreachable
rotl a u (Node More (Node Same x m y) v c) = L(Node Same (Node Same a u x) m (Node Same y v c))
rotl a u (Node More (Node Less x m y) v c) = L(Node Same (Node More a u x) m (Node Same y v c))
rotl a u (Node More (Node More x m y) v c) = L(Node Same (Node Same a u x) m (Node Less y v c))

delMin :: Avl (S n) -> (Int, (Avl n + Avl (S n)))
delMin Tip = unreachable
delMin (Node Less Tip x r) = (x,L r)
delMin (Node Same Tip x r) = (x,L r)
delMin (Node More Tip x r) = unreachable
delMin (Node bal (l@(Node _ _ _ _)) x r) = 
      case delMin l of
        (y,R l) -> (y,R(Node bal l x r))
        (y,L l) ->
          case bal of
            Same -> (y,R(Node Less l x r))
            More -> (y,L(Node Same l x r))
            Less -> (y,rotl l x r)

del :: Int -> Avl n -> (Avl n + exists m .(Equal (S m) n,Avl m))
del y Tip = L Tip
del y (Node bal l x r)
  | y == x = case r of
             Tip ->  
               case bal of
                 Same -> R(Ex(Eq,l))
                 More -> R(Ex(Eq,l))
                 Less -> unreachable
             Node _ _ _ _ ->
               case (bal,delMin r) of
                 (_,z,R r) -> L(Node bal l z r)
                 (Same,z,L r) -> L(Node More l z r)
                 (Less,z,L r) -> R(Ex(Eq,Node Same l z r))
                 (More,z,L r) -> 
                    case rotr l z r of
                      L t -> R(Ex(Eq,t))
                      R t -> L t
  | y < x = case del y l of
            L l -> L(Node bal l x r)
            R(Ex(Eq,l)) -> 
              case bal of
                Same -> L(Node Less l x r)
                More -> R(Ex(Eq,Node Same l x r))
                Less -> 
                   case rotl l x r of
                     L t -> R(Ex(Eq,t))
                     R t -> L t
  | y > x = case del y r of
            L r -> L(Node bal l x r)
            R(Ex(Eq,r)) -> 
              case bal of
                Same -> L(Node More l x r)
                Less -> R(Ex(Eq,Node Same l x r))
                More -> 
                   case rotr l x r of
                     L t -> R(Ex(Eq,t))
                     R t -> L t

delete :: Int -> AVL -> AVL
delete x (AVL t) = case del x t of L t -> AVL t; R(Ex(Eq,t)) -> AVL t

--------------------------------------------------------------------------------
-- alternate way to type del

data DelAns:: Nat ~> *0 where
 NotShrunk :: Avl n -> DelAns n
 Shrunk :: Avl n -> DelAns (S n)

del_ :: Int -> Avl n -> DelAns n
del_ y Tip = NotShrunk Tip
del_ y (Node bal l x r)
  | y==x = case r of
             Tip ->  
               case bal of
                 Same -> Shrunk l
                 More -> Shrunk l
                 Less -> unreachable
             Node _ _ _ _ ->
               case (bal,delMin r) of
                 (_,z,R r) -> NotShrunk(Node bal l z r)
                 (Same,z,L r) -> NotShrunk(Node More l z r)
                 (Less,z,L r) -> Shrunk(Node Same l z r)
                 (More,z,L r) -> 
                    case rotr l z r of
                      L t -> Shrunk t
                      R t -> NotShrunk t

delete_ :: Int -> AVL -> AVL
delete_ x (AVL t) = case del_ x t of Shrunk t -> AVL t; NotShrunk t -> AVL t

