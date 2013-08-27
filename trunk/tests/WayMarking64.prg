import "../src/LangPrelude.prg"

data Mark = FullStop | Stop | Digit Bool

data Way = Arrived | Step Mark Way deriving List(w)

etalon = "1s100000s11010s10100s1111s1010s110s11s1S"

w1 = [FullStop]w
w2 = [Digit True, FullStop]w
w3 = [Stop, Digit True, FullStop]w

countSteps (way@[_;_]w) = howmanysteps 0 way

howmanysteps :: Int -> Way -> Int
howmanysteps 0 []w = 0
howmanysteps corr [FullStop]w = corr + 1
howmanysteps corr [Stop, Digit True; way]w = pickupMarks (trace ("corr: "++show corr) corr + 2) way 1
  where pickupMarks corr [FullStop]w acc = corr + acc
        pickupMarks corr [Stop; _]w acc = trace (show corr) corr + acc
        pickupMarks corr [Digit False; more]w acc = pickupMarks (corr + 1) more $ acc + acc
        pickupMarks corr [Digit True; more]w acc = pickupMarks (corr + 1) more $ acc + acc + 1
howmanysteps corr [Digit _; more]w = howmanysteps (corr + 1) more


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

