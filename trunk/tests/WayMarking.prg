import "../src/LangPrelude.prg"

data Mark = FullStop | Stop | Digit Bool

data Way = Arrived | Step Mark Way deriving List(w)

etalon = "1s100000s11010s10100s1111s1010s110s11s1S"

w1 = [FullStop]w
w2 = [Digit True, FullStop]w
w3 = [Stop, Digit True, FullStop]w

countSteps = howmanysteps 0

howmanysteps :: Int -> Way -> Int
howmanysteps corr [FullStop]w = corr + 1
howmanysteps corr [Stop, Digit True; way]w = corr + pickupMarks way 1
  where pickupMarks [FullStop]w acc = acc
        pickupMarks [Stop; _]w acc = acc
        pickupMarks [Digit False; more]w acc = pickupMarks more $ acc + acc
        pickupMarks [Digit True; more]w acc = pickupMarks more $ acc + acc + 1
howmanysteps corr [Digit _; more]w = howmanysteps (corr + 1) more


l2w = foldr (Step . c2m) Arrived
  where c2m 'S' = FullStop
        c2m 's' = Stop
        c2m '0' = Digit False
        c2m '1' = Digit True

etalon' = l2w etalon
