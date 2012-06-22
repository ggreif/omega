-- first example from issue 91
--
f :: ((forall x. Bool) -> Int) -> Bool -> Int                                   
f x = x


-- second example from issue 91
--
kind X k = A k                                                                  
                                                                                
data Token :: k ~> *0 where                                                     
  Token :: forall (k :: *1) (a :: k). Token a                                   
                                                                                
x :: Token (A a)                                                                
x = Token :: Token (A a)

