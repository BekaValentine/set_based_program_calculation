## Reasoning via programmer-as-spec

Suppose we want to define a reverse function, having no clue how to define it
on cons lists. But we do know how to tell if a list is the reverse of another
list, and we can judge the general patterns we might right. For instance, we
can say `reverse [0,1,2,3] == [3,2,1,0]` ought to be true, and in general that
`reverse [x0, x1, x2, ..., xn] == [xn, ..., x2, x1, x0]`. I'm using `==` here
as denotational equality not computational equality.

Given this, let's make a guess that reverse is indeed definable, and moreover
that it's definiable via a foldr. If so, then by the universal property of
foldr, it must be the case that `reverse == foldr c n` is true if and only
if `reverse [] == n` and also `reverse (x:xs) == c x (reverse xs)`

Well, we can reason on each equation as follows:

```haskell
    n
== { half of the UMP }
    reverse []
== { programmer's intuitions }
    []
```

And thus, `n == []`, which is trivial to solve by defining `n = []`.

For the other case, it's a little more nuanced. We don't know what `xs` is, but
we can use the programmer's intuitions again to say that its _some_ list
`[x1, x2, x3, ..., xn]`. Then by intuition:

```haskell
    reverse (x : [x1, x2, x3, ..., xn])
== { definition of list sugar }
    reverse [x, x1, x2, x3, ..., xn]
== { programmer's intuition }
    [xn, ..., x3, x2, x1, x]
== { familiarity with append }
    [xn, ..., x3, x2, x1] ++ [x]

-- but also

    reverse (x : [x1, x2, x3, ..., xn])
== { the UMP }
    c x (reverse [x1, x2, x3, ..., xn])
== { programmer's intuition }
    c x [xn, ..., x3, x2, x1]

-- so

    c x [xn, ..., x3, x2, x1]
== { the above two }
    [xn, ..., x3, x2, x1] ++ [x]
```

And so by the fact that `[x1, x2, x3, ..., xn]` is just proxy for `reverse xs`, we have

```haskell
c x (reverse xs) == reverse xs ++ [x] 
```

This can be solved trivially by abstracting over `reverse xs` and defining
`c x xs = xs ++ [x]`.

Now we've arrived at our definitions for both arguments to fold, so:

```haskell
reverse = foldr c n
    where
        n = []
        c x xs = xs ++ [x]
```
This is obviously inefficient, but that's a problem for optimization techniques,
not for definition techniques.


## Reasoning to find inverses via sets

Suppose that we want to calculate some functions for binary trees defined as

```haskell
data Tree
    = Leaf
    | Branch Tree Tree
```

In particular, suppose we have a size function, and want to calculate all the
trees of a given size:

```haskell
size :: Tree -> Nat
size Leaf = 0
size (Branch l r) = Suc (size l + size r)

genSize :: Nat -> [Tree]
genSize = _
```

And we want to have the constraint hold that for all `n` and `t`, if `t` is in
`genSize n`, then `size t == n`. I'm using `==` here as denotational equality
rather than computational equality, and distinct from Haskell's definitional
equality `=`.

Then we'll reason as follows: firstly, we'll treat `[Tree]` as sets just so
that we can lean on set notation as needed, and treat it as `P Tree`, the
powerset of trees.

Second, the constraint gives us an equational specification:

```haskell
genSize n == { t :: Tree | size t == n }
```

Now, how can we proceed? By clever use of guessing, let's suppose that
`genSize` is in fact computable via case analysis on `n`. So the first casemust
therefore be

```haskell
    genSize 0
== { by definition of genSize }
    { t :: Tree | size t == 0 }
== { by definition of Tree }
    { t :: Tree | (t == Leaf \/ exists l r. t == Branch l r) /\ size t == 0 }
== { by DeMorgan }
    { t :: Tree | (t == Leaf /\ size t == 0) \/
                  (exists l r. t == Branch l r /\ size t == 0 ) }
== { by definition of union }
    { t :: Tree | t == Leaf /\ size t == 0 } U
    { t :: Tree | exists l r. t == Branch l r /\ size t == 0 }
== { by substitution of equals }
    { Leaf | size Leaf == 0 } U
    { Branch l r | exists l r. size (Branch l r) == 0 }
== { by definition of size }
    { Leaf | 0 == 0 } U
    { Branch l r | exists l r. Suc (size l + size r) == 0 }
== { by equality on Nat }
    { Leaf } U
    { Branch l r | exists l r. False }
== { by existentials }
    { Leaf } U
    { Branch l r | False }
== { by comprehension }
    { Leaf } U
    {}
== { by definition of union }
    { Leaf }
```

And so we've come to the equation `genSize 0 == { Leaf }`.

Similar reasoning gets us to

```haskell
    genSize (Suc n)
== { by similar reasoning }
    { Branch l r | exists l r. size (Branch l r) == Suc n }
== { by definition of size }
    { Branch l r | exists l r. Suc (size l + size r) == Suc n }
== { by equality on Nat }
    { Branch l r | exists l r. size l + size r == n }
== { by existentials and substitution of equals }
    { Branch l r | exists l r m p.
                    size l == m /\
                    size r == p /\
                    m + p == n }
== { by hypothesizing or having splits :: Nat -> P (Nat,Nat) }
    { Branch l r | exists l r m p.
                    size l == m /\
                    size r == p /\
                    (m,p) in splits n }
== { by definition of genSize }
    { Branch l r | exists l r m p.
                    l in genSize m /\
                    r in genSize p /\
                    (m,p) in splits n }
```

So we're now led to another equation

```haskell
genSize (Suc n) == { Branch l r |
                    exists m p.
                        (m,p) in splits n} /\
                        l in genSize m /\
                        r in genSize p }
```

Assuming splits satisfies the constraint `(m,p) in splits n iff m + p == n`,
then we have code that's straightforwardly recursive:

```haskell
genSize 0 = [ Leaf ]
genSize (Suc n) = [ Branch l r |
                    (m,p) <- splits,
                    l <- genSize m,
                    r <- genSize p ]
```

Defining `splits` by the same mechanism is relatively easy by similar reasoning.