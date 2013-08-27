import "../src/LangPrelude.prg"

data TwoBits = OO | OI | IO | II

data Mark = FullStop | Stop TwoBits | Digit TwoBits

data Way = Arrived | Step Mark Way deriving List(w)

etalon = "qrs13qrsqrsS"
--111 101 011 110 111 101 011 111 101 011 001


w1 = [FullStop]w
w2 = [Stop OI, FullStop]w
w3 = [Stop IO, Stop OI, FullStop]w
w4 = [Stop II, Stop IO, Stop OI, FullStop]w
w5 = [Stop OI, Stop II, Stop IO, Stop OI, FullStop]w
w6 = [Stop IO, Stop OI, Stop II, Stop IO, Stop OI, FullStop]w
w7 = [Stop II, Stop IO, Stop OI, Stop II, Stop IO, Stop OI, FullStop]w
w9 = [Digit OI, Digit II, Stop II, Stop IO, Stop OI, Stop II, Stop IO, Stop OI, FullStop]w
w12 = [Stop II, Stop IO, Stop OI, Digit OI, Digit II, Stop II, Stop IO, Stop OI, Stop II, Stop IO, Stop OI, FullStop]w

countSteps (way@[_;_]w) = howmanysteps 0 way

howmanysteps :: Int -> Way -> Int
howmanysteps 0 []w = 0
howmanysteps corr [FullStop]w = corr + 1
howmanysteps corr [Stop OI; way]w = pickupMarks (corr + 1) way 0
howmanysteps corr [Stop IO, Stop OI; way]w = pickupMarks (corr + 2) way 0
howmanysteps corr [Stop II, Stop IO, Stop OI; way]w = pickupMarks (corr + 3) way 0
howmanysteps corr [Digit OI,_,_; more]w = howmanysteps (corr + 3) more

pickupMarks corr [FullStop]w acc = corr + 1
pickupMarks corr [Stop _; _]w acc = corr + acc
pickupMarks corr [Digit OO; more]w acc = pickupMarks (corr + 1) more $ 4 * acc
pickupMarks corr [Digit OI; more]w acc = pickupMarks (corr + 1) more $ 4 * acc + 1
pickupMarks corr [Digit IO; more]w acc = pickupMarks (corr + 1) more $ 4 * acc + 2
pickupMarks corr [Digit II; more]w acc = pickupMarks (corr + 1) more $ 4 * acc + 3

{-
l2w = foldr (Step . c2m) Arrived
  where c2m 'S' = FullStop
        c2m 's' = Stop
        c2m '0' = Digit False
        c2m '1' = Digit True


foldw :: (Mark -> b -> b) -> b -> Way -> b
foldw _ b []w = b
foldw f b [m; ms]w = f m $ foldw f b ms


w2l = foldw ((:) . m2c) []
  where m2c FullStop = 'S'
        m2c Stop = 's'
        m2c (Digit False) = '0'
        m2c (Digit True) = '1'

etalon' = l2w etalon


countAlongTheWay = foldw tupled (0,[(0,[]w)])
  where tupled m (c, l@[(_,w);_]) = (countSteps [m;w]w, (countSteps [m;w]w,[m;w]w) : l)

-}