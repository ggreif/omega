# Background #

Back when I had time to participate in [ICFP contests](http://www.cs.cornell.edu/icfp/task.htm), there was a stack based language for describing scenes to be rendered with a ray tracer. I wrote a small compiler for this language and it was much fun. One of the interesting things was that recursion was not possible by calling the function being defined but you could invoke functions that were passed to them as arguments. So a simple trick was employed to get the _effect_ of recursion.

# The Trick #

Consider the the following faculty function:
```
fak n = if n == 1 then 1 else n * fak (n - 1)
```

The version without mentioning _fak_ in the body would be:
```
fak f n = if n == 1 then 1 else n * f f (n - 1)
```

Now, you have to call this function in a different way:
```
fak fak 5
  ==> 120
```

So the upper _fak_ is equivalent to the lower _fak fak_.

# The Idea #

The above trick does work in a dynamically typed language but, traditional static type systems fail to assign a type to the second _fak_, as the type would be infinite.
My crazy idea is to allow infinite types in special cases. The below sections try to elaborate this idea. But be warned: it may well lead to nothing.

## The Quest for the Infinite Type ##

Now let's try to determine a type for the second _fak_ (my running theme). In first approximation it would be
```
fak :: (a -> Int -> Int) -> Int -> Int
```

But of course this would let us only compute _fak fak 2_ but not _fak fak 3_! Why? Because _a_ does not correctly type the first argument in the second unfolding.

## Making the Jump ##

We have to let loose to find the correct type. Because the unfolding may happen any times, _a_ must be infinitely expanded to be _a -> Int -> Int_ (note that this again contains an _a_!).

## And Sized Types? ##

We can try to extend this scheme to size types. Let's change our running example to the conversion _Nat' n -> Int_. Here is the code:
```
conv :: Nat' n -> Int
conv 0v = 0
conv (1 + n)v = 1 + conv n
```
We can interpret this function as a family of distinct functions indexed by _n_ and each being monomorphic:
```
conv{0} :: Nat' 0t -> Int
conv{0} 0v = 0
conv{1+n} :: Nat' (1 + n)t -> Int
conv{1+n} (1 + n)v = 1 + conv{n} n
```


## Mutual recursion ##


## Other Implementations ##

Andreas Abel has released code and a companion paper for his [MiniAgda](http://www2.tcs.ifi.lmu.de/~abel/par10.pdf) system. He employs sized types to prove termination of recursive functions and coinductive algorithms' productivity.
The funny thing is that he tracks the sizes in a very similar manner as me above. His size parameter is currently exposed to the algorithm in first position, but he expects to hide it. It is a value, but must be used parametrically (not referencable from the value world).