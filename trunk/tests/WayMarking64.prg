import "../src/LangPrelude.prg"

data TwoBits = OO | OI | IO | II

data Mark = FullStop | Stop TwoBits | Digit TwoBits

data Way = Arrived | Step Mark Way deriving List(w)

etalon = "qrs101qrs30qrs13qrs3rsS"
-- acc:   55555544455444443332221

w1 = [FullStop]w
w2 = [Stop OI, FullStop]w
w3 = [Stop IO, Stop OI, FullStop]w
w4 = [Digit II, Stop IO, Stop OI, FullStop]w
w5 = [Stop OI, Digit II, Stop IO, Stop OI, FullStop]w
w6 = [Stop IO, Stop OI, Digit II, Stop IO, Stop OI, FullStop]w
w7 = [Stop II, Stop IO, Stop OI, Digit II, Stop IO, Stop OI, FullStop]w
w9 = [Digit OI, Digit II, Stop II, Stop IO, Stop OI, Digit II, Stop IO, Stop OI, FullStop]w
w12 = [Stop II, Stop IO, Stop OI, Digit OI, Digit II, Stop II, Stop IO, Stop OI, Digit II, Stop IO, Stop OI, FullStop]w
w13 = [Digit OO, Stop II, Stop IO, Stop OI, Digit OI, Digit II, Stop II, Stop IO, Stop OI, Digit II, Stop IO, Stop OI, FullStop]w
w14 = [Digit II, Digit OO, Stop II, Stop IO, Stop OI, Digit OI, Digit II, Stop II, Stop IO, Stop OI, Digit II, Stop IO, Stop OI, FullStop]w
w15 = [Stop OI, Digit II, Digit OO, Stop II, Stop IO, Stop OI, Digit OI, Digit II, Stop II, Stop IO, Stop OI, Digit II, Stop IO, Stop OI, FullStop]w

countSteps (way@[_;_]w) = howmanysteps 0 way

howmanysteps :: Int -> Way -> Int
howmanysteps 0 []w = 0
howmanysteps corr [FullStop]w = corr + 1
howmanysteps corr [Stop OI; way]w = pickupMarks (corr + 1) way 0
howmanysteps corr [Stop IO, Stop OI; way]w = pickupMarks (corr + 2) way 0
howmanysteps corr [Stop II, Stop IO, Stop OI; way]w = pickupMarks (corr + 3) way 0
howmanysteps corr [Digit _,_,_; more]w = howmanysteps (corr + 3) more

pickupMarks corr [FullStop]w acc = corr + 1
pickupMarks corr [Stop _; _]w acc = corr + acc
pickupMarks corr [Digit OO; more]w acc = pickupMarks (corr + 1) more $ 4 * acc
pickupMarks corr [Digit OI; more]w acc = pickupMarks (corr + 1) more $ 4 * acc + 1
pickupMarks corr [Digit IO; more]w acc = pickupMarks (corr + 1) more $ 4 * acc + 2
pickupMarks corr [Digit II; more]w acc = pickupMarks (corr + 1) more $ 4 * acc + 3

l2w = foldr (Step . c2m) Arrived
  where c2m 'S' = FullStop
        c2m 's' = Stop OI
        c2m 'r' = Stop IO
        c2m 'q' = Stop II
        c2m '0' = Digit OO
        c2m '1' = Digit OI
        c2m '2' = Digit IO
        c2m '3' = Digit II


foldw :: (Mark -> b -> b) -> b -> Way -> b
foldw _ b []w = b
foldw f b [m; ms]w = f m $ foldw f b ms


w2l = foldw ((:) . m2c) []
  where m2c FullStop = 'S'
        m2c (Stop OI) = 's'
        m2c (Stop IO) = 'r'
        m2c (Stop II) = 'q'
        m2c (Digit OO) = '0'
        m2c (Digit OI) = '1'
        m2c (Digit IO) = '2'
        m2c (Digit II) = '3'


waylen = foldw (\_ n->n+1) 0

etalon' = l2w etalon

countAlongTheWay = foldw tupled [(0,[]w)]
  where tupled m (l@[(_,w);_]) = (countSteps [m;w]w,[m;w]w) : l

prepend :: Int -> Way -> Way
prepend 0 acc = acc
prepend n acc | n `mod` 4 == 0 = prepend (n `div` 4) [Digit OO; acc]w
prepend n acc | n `mod` 4 == 1 = prepend (n `div` 4) [Digit OI; acc]w
prepend n acc | n `mod` 4 == 2 = prepend (n `div` 4) [Digit IO; acc]w
prepend n acc | n `mod` 4 == 3 = prepend (n `div` 4) [Digit II; acc]w

-- builds a way of length at least 'min'
-- maintains the invariant, that the way starts with 'Stop II'
--
construct :: Int -> Way -> Way
construct min (acc@[Stop II; _]w) = if l < min
                                    then construct min $ [Stop II, Stop IO, Stop OI; prepend l acc]w
                                    else acc
  where l = waylen acc
