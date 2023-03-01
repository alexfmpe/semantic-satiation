DRAFT
========

Filtering constraints
========

A common formulation for a filtering class is

```haskell
class Filterable f where
  filter :: (a -> Bool) -> f a -> f a

Distributivity
  filter f . filter g = filter (\x -> f x && g x)

Identity
  filter (const True) = id
```

which relies on parametricity of `(* -> *)` types. This rules out "obvious" use cases like `ByteString` and `Text`, and often `Functor` is a superclass, throwing `Set` out the window as well.
As it turns out, if we narrow down the laws enough, there's no need to care about the specific arity/kind. Note the identity law will force the second argument and the return to have unifiable types, so we can parametrize things as much as needed, via `MultiParamTypeClasses` or associated type families, and constrain via semantics rather than via syntax.

This is a literate haskell file, so we start by getting the extensions/imports out of the way.

```haskell
> {-# LANGUAGE CPP #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE TypeFamilies #-}
> import Prelude hiding (filter)
> import Data.ByteString (ByteString)
> import Data.ByteString qualified as ByteString
> import Data.Functor.Const
> import Data.List qualified as List
-- > import Data.Dependent.Map (DMap)
-- > import Data.Dependent.Map qualified as Dependent.Map
> import Data.Map (Map)
> import Data.Map qualified as Map
> import Data.Set (Set)
> import Data.Set qualified as Set
> import Data.Text (Text)
> import Data.Text qualified as Text
> import Data.Word (Word8, Word16)
```

Instead of the usual we'll do

<!--
-- #ifdef FILTER_FUNDEPS
-->
```haskell
> class Filterable f a | f -> a where
>   filter :: (a -> Bool) -> f -> f

> instance Filterable [a] a where
>   filter = List.filter

> instance Filterable (Set a) a where
>   filter = Set.filter

> instance Filterable Text Char where
>   filter = Text.filter

> instance Filterable ByteString Word8 where
>   filter = ByteString.filter
```
and play the obnoxious nitpicking adversary by throwing intuitively wrong instances at it until we figure out the correct constraints.

No more, no less
--------
The usual laws prevent us from "under-filtering", as

```haskell
instance Filterable [a] a where
  filter p xs = case any p xs of
    True -> xs
    False -> []
```
contradicts _Distributivity_

```haskell
    (filter odd . filter even) [1,2] = filter (\x -> odd x && even x) [1,2]
<=> (filter odd) [1,2] = filter (const False) [1,2]
<=> [1,2] = []
```

But what about "over-filtering"?

```haskell
instance Filterable [a] a where
  filter p xs = case all p xs of
    True -> xs
    False -> []
```

Why is this a problem? Because we want each element to either be thrown out or kept depending exclusively on what it's mapped to by the predicate.
With these loose instances we're even allowing mutually exclusive predicates to cause the same filtering.
We address this by also requiring that if a value can be filtered to multiple ones, then mutually exclusive predicates must be mapped to different values:

```haskell
Soundness
  forall xs. exists p. filter p xs = filter (not . p) xs <=> (forall h. xs = filter h xs)
```

Liberties constrain, constraints liberate
--------
We lose parametricity and thus free theorems, which means more care must be taken with laws. The extra parameter brings the freedom to do silly things like

```haskell
> dup :: a -> (a,a)
> dup a = (a,a)

instance Filterable ByteString (Word8, Word8) where
  filter p = ByteString.filter (p . dup)
```

Clearly the supplied predicate is an overly loose fit as only it's "diagonal" is ever evaluated. What we actually want is for the predicate's target type to have exactly as much structure as needed to satisfy the laws, and no more.
We can enforce this via a [universal property](https://en.wikipedia.org/wiki/Universal_property).
Namely, if there's a unique way to "detour" the given predicate through another law-abiding one, then the other one is "better".
We require the "best" such predicate, or that all such "best" are all equivalent/isomorphic.

Note there's no unique way to implement `ByteString.filter` with `Silly.filter`, since the `Silly` one has an extra redundant `Word8` floating around.
```haskell
  ByteString.filter p = Silly.filter (p . fst)
  ByteString.filter p = Silly.filter (p . snd)
```

The resulting law is
```haskell
  forall f. (exists unique g. f (p . g) = filter p) => g = id
```

Put another way, given a partial order over law-abiding filter functions with ```f1 <= f2``` meaning ```f1 (p . g) = f2 p```, we take a minimal implementation, as it is _equivalent_ (sufficient and necessary) to lawfulness.

What about an overly tight fit? Pretend there's some `Word4` type representing a nibble
```haskell
instance Filterable ByteString Word4 where
  filter p = ByteString.filter (p . fromIntegral . (`div` 16)) -- Or `mod` for the other nibble
```

We can implement this behavior uniquely in terms of `ByteString.filter`, but not the other way around. There's just no way to shoehorn a predicate that distinguishes between 2^8 values into a lower "resolution" one that can only deal with 2^4. However, all this applies only when we're trying to match the types directly one-to-one. Clearly the following exist

```haskell
  instance Filterable [(Word8, Word8)] (Word8, Word8)
  instance Filterable [Word4] Word4
```

so why can't we do something similar? Well, for `Word4` we'd be splitting each `Word8` in two and independently applying the predicate, but the action taken (keep or drop) wouldn't be independent so we'd violate _Soundness_. For our uncurried `Word16`, we'd need to grab bytes in pairs, which we could filter atomically. However, this breaks down once we consider odd lengths. What would this filter do when given a predicate and a singleton? If we don't apply the predicate to the element we have a `const`. We need to always return the singleton or break _Identity_. Thus we end up stuck on a non-empty bytestring. Since the `Word8` implementation allows making further "progress", another partial order suggests itself, from which we again pick the minimal:

```haskell
  (forall p. filter p xs = xs) => (forall f p. f p xs = xs)
```

Meaning, the canonical filter is able to throw out everything that can be thrown out. Let's call this the _Completeness_ law.

Backtracking just a bit, note that with the universal property we can also reject the trivial instance
```haskell
instance Filterable [a] a where
  filter p xs = xs
```

since
```haskell
Trivial.filter p = List.filter $ const True . p
```
but `List.filter` can't be factored in terms of `Trivial.filter`

What's more interesting is that this criterion prevents not just the whole, but *any* part of the structure from escaping the filter semantics:

```haskell
> data A x y = A [x] [y]
```

```haskell
module Good

> instance Filterable (A x y) (Either x y) where
>  filter p (A xs ys) = A
>    (List.filter (p . Left) xs)
>    (List.filter (p . Right) ys)
```

```haskell
module Bad

instance Filterable (A x y) (Either x y) where
  filter p (A xs ys) = A
    (List.filter (p . Left) xs)
    ys
```

`Bad.filter` would not be valid, as it can be factored by `Good.filter` but not the other way around.

```haskell
Bad.filter p = Good.filter $ either (p . Left) (const True)
```

All the way down
--------
For many types an additional law holds: `filter (const False) = const x`. We can model this with

```haskell
class Filterable f a => Rooted f where
  -- Law: absorbing element
  --   filter (const False) = const root
  root :: f
```
...well, not quite, as that gives us `error: Not in scope: type variable ‘a’`, since `Rooted` doesn't involve the type that's targeted by the predicate.
This can be fixed by instead using an associated type family:

```haskell
> class FilterableX f where
>  type PredicateTarget f :: *
>  filterX :: (PredicateTarget f -> Bool) -> f -> f

class Filterable f => Rooted f where
 root :: f

instance Rooted Text where
  root = Text.empty

instance Rooted [a] where
  root = []
```

<!--
-- #endif
-->

Here's a [counterexample](https://blog.functorial.com/posts/2015-12-06-Counterexamples.html) of a type that is `Filter` but not `Rooted`:
```haskell
data NotRooted b a = NotRooted b [a]
instance Filterable (NotRooted a) where
  type PredicateTarget (NotRooted a) = a
  filter p (NotRooted b xs) = NotRooted b (filter p xs)
```

The universal property prevents us from not filtering the array, and polymorphism prevents us from knowing anything about, and thus doing anything to the `b` value. The existance of a `Rooted` instance implies a contradiction:
```haskell
    filter (const False) (NotRooted b xs) = root = filter (const False) (NotRooted b' xs)
<=> NotRooted b (filter (const False) xs) = root = NotRooted b' (filter (const False) xs)
<=> NotRooted b [] = root = NotRooted b' []
==> NotRooted True [] = NotRooted False []
```

Through the looking glass
--------

So far we've only seen `filter` on covariant types. We can think of these as producers of values. When the predicate rejects a value, the filtered structure won't produce that value. Mutatis mutandis, filtering a contravariant type allows us to restrict the values that are consumed.

But what does that really mean? Let's look at an example from `Data.Functor.Contravariant`
```haskell
newtype Predicate a = Predicate { getPredicate :: a -> Bool }
```

If we think of this as an [indicator function](https://en.wikipedia.org/wiki/Indicator_function), then it's reminiscent of `Data.Set.Set`. The element is in the set iff `getPredicate p a = True`.
That is, filtering out an element from this implicit set results in a new `Predicate` for which `getPredicate p' a = False`.
What happens if we filter them all out? We're left with `Predicate (const False)`.

```haskell
instance Filterable (Predicate a) where
  type PredicateTarget (Predicate a) = a -- hello there semantic satiation
  filter p (Predicate q) = Predicate (\x -> p x && q x)
instance Rooted (Predicate a) where
  root = Predicate (const False)
```

Now we see what it means not to consume a value - we adopt the behavior of `const` locally. We decide what the output is, even without looking at the input.

Moving on to
```haskell
newtype Equivalence a = Equivalence { getEquivalence :: a -> a -> Bool }
```

What does filtering this look like? Let's think about `filter (const False)`.
Since this results in an `Equivalence` that cannot inspect any input, then we must decide whether to always return `True` or `False`.

Taking into account the reflexivity law (`getEquivalence' f a a = True`) leaves us with only one option.
Now we know that empty here is `Equivalence $ \_ _ -> True`, a single equivalence class with all the elements.

In other words, filtering an `Equivalence` introduces a new equivalence class which contains exactly the elements for which the predicate failed.

```haskell
instance Filterable (Equivalence a) where
  type PredicateTarget (Equivalence a) = a
  filter p (Equivalence f) = Equivalence $ \a b -> case (p a, p b) of
    (True, True) -> f a b
    (False, False) -> True
    _ -> False
```

Similary to the covariant situation, the predicate controls which values can be used. Each time the predicate fails, we throw out information.

What is variance
--------
So far we've only seen instances for glorified sequences and sets, types whose components can be thrown out independently. Things get more interesting when they can't. It's common to have the equivalent of
```haskell
instance Filterable (Map k v) v where
-- >   type PredicateTarget (Map k v) = v
 filter = Map.filter
```

but this actually violates our universal property, which instead demands
```haskell
instance Filterable (Map k v) (k,v) where
-- >   type PredicateTarget (Map k v) = v
  filter p = Map.filterWithKey (curry p)
```

since
```haskell
  Map.filter p = Map.filterWithKey (p . curry snd)
```
but we can't do the predicate factoring in the other direction. Let's wrap things up with the higher-ranked version

```haskell
instance Filterable (DMap k v) (DSum k v) where
  filter p = DMap.filterWithKey $ \(k, v) -> p (k :=> v)

instance Rooted (Map k v) where
  root = Map.empty

instance GCompare k => Rooted (DMap k v) where
  root = DMap.empty
```

The road ahead
--------

Ok, so all those annoying laws did bring benefits - we won't need separate filter hierarchies to handle monomorphism/higher-rank/variance/arity variants. However, this expels us from the protective shelther of `Data.Functor`. The `Map` instance might raise an eyebrow if you're used to some sort of `mapMaybe :: (a -> Maybe b) -> f a -> f b` linking filtering and mapping together. Even the free theorem for `filter :: (a -> Bool) -> [a] -> [a]` states `forall y. fmap g (filter (q . g) y) = filter q (fmap g y))`.

In the next post we'll re-evaluate these connections to find out how the tricks used here can figure into other household classes

A special thanks to libraries (well, to authors/maintainers/contributors) in this area which heavily influenced both the problems and solutions in this post.
- [contravariant](https://hackage.haskell.org/package/contravariant)
- [mono-traversable](https://hackage.haskell.org/package/mono-traversable)
- [rank2classes](https://hackage.haskell.org/package/rank2classes)

- [compactable](https://hackage.haskell.org/package/compactable)
- [witherable](https://hackage.haskell.org/package/witherable)
