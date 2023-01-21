Everything you never wanted to know about Applicative laws and more
========

[Applicative Programming with Effects](https://www.staff.city.ac.uk/~ross/papers/Applicative.html) introduced the concept of `Applicative` alongside two sets of laws, while [@duplode](https://github.com/duplode) presented a third in [Applicative Archery](https://duplode.github.io/posts/applicative-archery.html), and yet another can be formulated in terms of `liftA2`.
Ultimately they all describe a binary function equipped with some sort of associativity-related property and has left/right identities.
This post explores the pros/cons of each viewpoint and proves these sets of laws are all equivalent. The names used are tentative at best, as usually only the first set is mentioned without need for distinguishing it.

Let's pretend [Data.Functor.Apply](https://hackage.haskell.org/package/semigroupoids-5.3.7/docs/Data-Functor-Apply.html#t:Apply) and [Control.Applicative](https://hackage.haskell.org/package/base-4.17.0.0/docs/Control-Applicative.html#t:Applicative) are defined as follows

<!--
> module Blog.ApplicativeLaws where
> import Data.Proxy
-->

```haskell
> import Control.Arrow ((***))
> import Prelude hiding (Applicative(..))

> class Functor f => Apply f where
>   liftA2 :: (a -> b -> c) -> f a -> f b -> f c
>   liftA2 f a b = fmap (uncurry f) (a ⊗ b)

>   infixl 4 ⊗
>   (⊗) :: f a -> f b -> f (a,b)
>   (⊗) = liftA2 (,)

>   infixl 4 <*>
>   (<*>) :: f (a -> b) -> f a -> f b
>   (<*>) = liftA2 ($)

>   infixl 4 <.>
>   (<.>) :: f (b -> c) -> f (a -> b) -> f (a -> c)
>   (<.>) = liftA2 (.)

> class Apply f => Applicative f where
>   unit :: f ()
>   unit = pure ()

>   pure :: a -> f a
>   pure a = fmap (const a) unit
```

Are these necessarily equivalent to the current definitions? We'll show it to be the case once we've proven some results about the laws.

The proofs use equational reasoning and are formatted with a sanity check that can check well-formedness. This prevents gibberish but doesn't stop us from being plain wrong.

```haskell
> infixl 0 ===
> (===) :: a -> a -> a
> (===) = const
```

To actually enforce correctness, fancier types would be needed. For example, see section _4 Equational reasoning in Agda_ of https://github.com/jespercockx/agda-lecture-notes/blob/master/agda.pdf

We'll also rely heavily on free theorems for the proofs, introducing them along the way. The theorems used in this post are obtained from lambdabot's `free` command, with minor formatting applied.
Note lambdabot's plugin uses a version of the [free-theorems package](https://hackage.haskell.org/package/free-theorems) that doesn't support type constructor variables, so a specific one (e.g. `[]`, `Maybe`) must be used. Any type constructor seems to always yield the same result, modulo names.

A version with support for the such variables lives in https://github.com/ichistmeinname/free-theorems, but [doesn't reduce relations into functions](https://github.com/ichistmeinname/free-theorems/issues/5). It's [not yet on hackage](https://github.com/ichistmeinname/free-theorems/issues/4) but you can see it at work by visiting https://www-ps.informatik.uni-kiel.de/~sad/FreeTheorems/cgi-bin/free-theorems-webui.cgi.

Monoidal formulation
---------------

```haskell
> assoc :: ((a,b), c) -> (a,(b, c))
> assoc ((a,b), c) = (a,(b, c))

Associativity
  u ⊗ (v ⊗ w) = fmap assoc ((u ⊗ v) ⊗ w)
Left Identity
  u = fmap snd (unit ⊗ u)
Right Identity
  u = fmap fst (u ⊗ unit)
```

These were introduced at the end of the original paper and are also described in the [Typeclassopedia](https://wiki.haskell.org/Typeclassopedia#Alternative_formulation).
The associative-ish law states that shuffling parenthesis around 'outside' results only in them being shuffled in the exact same shape 'inside', so we can go back and forth with impunity.

The free theorem for `(⊗)` is

```haskell
fmap g u ⊗ fmap h v = fmap (g *** h) (u ⊗ v)
```

Note this reveals the ability to separate calls to `fmap` from calls to `⊗`. Together with the functor laws for identity and composition, this means we can take any combination of those two operations and canonicalize it into a single `fmap` applied to a tree of `⊗`. That is, applying the 'inside' functions can be done before/after pairing up the 'outside' shapes or interspersed in any way between multiple pairings.

Furthermore, the associative law lets us apply tree rotations (shuffling the parenthesis), by applying the inverse rotations inside the lambda, with `,` as the binary operation instead of `⊗ = liftA2 (,)`. This gives us another layer of canonicalization, as we can now reduce to a single `fmap` applied to what's essentially a list/sequence of `⊗` if we push the parenthesis all the way to the right, as an `infixr` operator would.

We'll use this over and over when proving equivalences between the sets of laws. The most common pattern is canonicalizing both sides of an equation and 'meeting in the middle' by proving the resulting forms equivalent.

Applicational formulation
---------------
```haskell
Identity
  pure id <*> v = v
Composition
  pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
Homomorphism
  pure f <*> pure x = pure (f x)
Interchange
  u <*> pure y = pure ($ y) <*> u
```

These are the better known laws, defined in terms of `<*>` and `pure`. However, they obfuscate the underlying monoidal structure since the arguments of `<*>`, like `$`, have assymetrical roles. Another issue is that `pure` prohibits use of them for `Apply`.

These don't refer to `Functor` at all, as they view `Applicative` as a whole, while the Monoidal formulation describes what Apply/Applicative brings to the table besides what `Functor` already does, same as when formulating the `Monad` laws in terms of `fmap`/`join` vs `>>=`.

Here, _Identity_ is equivalent to the _Monoidal_ left identity

```haskell
> identity :: Applicative f => f a -> f a
> identity f =
>       pure id <*> f
>   === fmap (const id) unit <*> f
>   === liftA2 ($) (fmap (const id) unit) f
>   === fmap (uncurry ($)) (fmap (const id) unit ⊗ f)
>   === fmap (uncurry ($)) (fmap (const id) unit ⊗ fmap id f)
>   === fmap (uncurry ($)) (fmap (const id *** id) (unit ⊗ f))
>   === fmap (uncurry ($) . (const id *** id)) (unit ⊗ f)
>   === fmap (\((), f') -> const id () $ id f') (unit ⊗ f)
>   === fmap (\((), f') -> f') (unit ⊗ f)
>   === fmap snd (unit ⊗ f)
>   === f
```

The haddocks for `Applicative` claim `fmap f x = pure f <*> x` is a consequence of these laws.
It is also always a consequence for "our" `pure`, courtesy of both left identity laws being equivalent.

```haskell
> mapViaAp :: Applicative f => (a -> b) -> f a -> f b
> mapViaAp f u =
>       pure f <*> u
>   === fmap (const f) unit <*> u
>   === liftA2 ($) (fmap (const f) unit) u
>   === fmap (uncurry ($)) (fmap (const f) unit ⊗ u)
>   === fmap (uncurry ($)) (fmap (const f) unit ⊗ fmap id u)
>   === fmap (uncurry ($) . (const f *** id)) (unit ⊗ u)
>   === fmap (\((), u') -> const f () $ id u') (unit ⊗ u)
>   === fmap (\((), u') -> f u') (unit ⊗ u)
>   === fmap (f . snd) (unit ⊗ u)
>   === fmap f (fmap snd (unit ⊗ u))
>   === fmap f u
```

If the laws implied a unique implementation, then equivalence of laws would also mean equivalence of implementations. They do not, as evidenced by `Applicative []` vs `ZipList []`.
It is then desirable to prove the default definitions in `Control.Applicative` still hold and we're not accidentally proving laws about different semantics. The one for `<*>` is the same (`($) = id`), so let's do `liftA2`

```haskell
> liftA2Impl :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
> liftA2Impl f x y =
>       liftA2 f x y
>   === fmap (uncurry f) (x ⊗ y)
>   === fmap (\(x', y') -> f x' y') (x ⊗ y)
>   === fmap (\(x', y') -> f x' $ id y') (x ⊗ y)
>   === fmap (uncurry ($) . (f *** id)) (x ⊗ y)
>   === fmap (uncurry ($)) (fmap f x ⊗ fmap id y)
>   === fmap (uncurry ($)) (fmap f x ⊗ y)
>   === liftA2 ($) (fmap f x) y
>   === fmap f x <*> y
>   === f <$> x <*> y
```

What about `unit`/`pure` ? Well, the following holds for any function with the type of `pure` given its free theorem: `fmap f . pure = pure . f`
```haskell
> pureImpl :: Applicative f => a -> f a
> pureImpl a =
>       pure a
>   === pure (const a ())
>   === (pure . const a) ()
>   === fmap (const a) (pure ())
```

So giving the name `unit` to  `pure ()` justifies tying these two together with the given default implementations.
But could we replace the pair altogether with another law-abiding one or is it unique?
It turns out that for a given `Apply`, there is at most a valid `Applicative`.

When there's a left and right identity, these must be the same, as combining them results in something equal to both.
```haskell
    l
  = l ∗ r
  = r
```

We'll do essentially the same with extra steps to deal with the `()`-tupling
```haskell
> unitUniqueness :: Applicative f => f () -> f () -> f ()
> unitUniqueness u v =
>       u
>   === fmap fst (u ⊗ v)
>   === fmap (\((), ()) -> ()) (u ⊗ v)
>   === fmap snd (u ⊗ v)
>   === v
```

So the definitions are the same, and we can just focus on the laws. Getting back on track, the equivalent of right identity with `<*>` is
```haskell
> identityRight :: Applicative f => f a -> b -> f a
> identityRight f a =
>       fmap const f <*> pure a
>   === fmap const f <*> fmap (const a) unit
>   === liftA2 ($) (fmap const f) (fmap (const a) unit)
>   === fmap (uncurry ($)) (fmap const f ⊗ fmap (const a) unit)
>   --- ...canonicalization steps...
>   === fmap (uncurry ($) . (const *** const a)) (f ⊗ unit)
>   === fmap (\(f', ()) -> const f' $ const a ()) (f ⊗ unit)
>   === fmap (\(f', ()) -> f') (f ⊗ unit)
>   === fmap fst (f ⊗ unit)
>   === f
```

Why is it missing from this formulation? It actually isn't, as _Interchange_ lets us exchange identities (as in, `unit`/`pure`, not `id`), deriving one from the other

```haskell
> identityExchange :: Applicative f => f a -> b -> f a
> identityExchange f a =
>       f
>   === fmap const f <*> pure a
>   === pure ($ a) <*> fmap const f
>   === fmap (uncurry ($)) (fmap (const ($ a)) unit ⊗ fmap const f)
>   === fmap (uncurry ($) . (const ($ a) *** const)) (unit ⊗ f)
>   === fmap (\((), f') -> const ($ a) () $ const f') (unit ⊗ f)
>   === fmap (\((), f') -> f') (unit ⊗ f)
>   === fmap snd (unit ⊗ f)
>   === pure id <*> f
>   === f
```

and in the other direction, having both identities gives us _Interchange_

```haskell
> interchange :: Applicative f => f (a -> b) -> a -> f b
> interchange u y =
>       u <*> pure y
>   === u <*> fmap (const y) unit
>   === liftA2 ($) u (fmap (const y) unit)
>   === fmap (uncurry ($)) (u ⊗ fmap (const y) unit)
>   === fmap (uncurry ($)) (fmap id u ⊗ fmap (const y) unit)
>   === fmap (uncurry ($)) (fmap (id *** const y) (u ⊗ unit))
>   === fmap (uncurry ($) . (id *** const y)) (u ⊗ unit)
>   === fmap (\(u', ()) -> id u' $ const y ()) (u ⊗ unit)
>   === fmap (\(u', ()) -> u' y) (u ⊗ unit)
>   === fmap (($ y) . fst) (u ⊗ unit)
>   === fmap ($ y) (fmap fst (u ⊗ unit))

>   === fmap ($ y) u

>   === fmap ($ y) (fmap snd (unit ⊗ u))
>   === fmap (($ y) . snd) (unit ⊗ u)
>   === fmap (\((), u') -> u' y) (unit ⊗ u)
>   === fmap (\((), u') -> const ($ y) () $ id u') (unit ⊗ u)
>   === fmap (uncurry ($) . ((const ($ y)) *** id)) (unit ⊗ u)
>   === fmap (uncurry ($)) (fmap ((const ($ y)) *** id) (unit ⊗ u))
>   === fmap (uncurry ($)) ((fmap (const ($ y)) unit) ⊗ fmap id u)
>   === fmap (uncurry ($)) ((fmap (const ($ y)) unit) ⊗ u)
>   === liftA2 ($) (fmap (const ($ y)) unit) u
>   === fmap (const ($ y)) unit <*> u
>   === pure ($ y) <*> u
```

We can show _Composition_ is associativity in an assymetrical disguise by reducing to the canonical form

```haskell
> composition :: Applicative f => f (b -> c) -> f (a -> b) -> f a -> f c
> composition u v w =
>       u <*> (v <*> w)
>   === liftA2 ($) u (liftA2 ($) v w)
>   === fmap (uncurry ($)) (u ⊗ fmap (uncurry ($)) (v ⊗ w))
>   === fmap (uncurry ($)) (fmap id u ⊗ fmap (uncurry ($)) (v ⊗ w))
>   === fmap (uncurry ($)) (fmap (id *** uncurry ($)) (u ⊗ (v ⊗ w)))
>   === fmap (uncurry ($) . (id *** uncurry ($))) (u ⊗ (v ⊗ w))
>   === fmap (\(u', (v', w')) -> u' (v' w')) (u ⊗ (v ⊗ w))
```

Now, to derive _Composition_ as the conclusion we proceed with

```haskell
>   === fmap (\(u', (v', w')) -> u' (v' w')) (u ⊗ (v ⊗ w))
>   === fmap (\((u', v'), w') -> u' (v' w')) ((u ⊗ v) ⊗ w)
>   === fmap (\((u', v'), w') -> (u' . v') $ id w') ((u ⊗ v) ⊗ w)
>   === fmap (uncurry ($) . (uncurry (.) *** id)) ((u ⊗ v) ⊗ w)
>   === fmap (uncurry ($)) (fmap (uncurry (.) *** id) ((u ⊗ v) ⊗ w))
>   === fmap (uncurry ($)) (fmap (uncurry (.)) (u ⊗ v) ⊗ fmap id w)
>   === fmap (uncurry ($)) (fmap (uncurry (.)) (u ⊗ v) ⊗ w)
>   === fmap (uncurry ($)) (liftA2 (.) u v ⊗ w)
>   === liftA2 ($) (liftA2 (.) u v) w
>   === liftA2 (.) u v <*> w
>   === (.) <$> u <*> v <*> w
```

but we can go the other way by taking it as the hypothesis in canonical form, that is,
```haskell
> compositionCanonicalized u v w =
>       fmap (\(u', (v', w')) -> u' (v' w')) (u ⊗ (v ⊗ w))
>   === fmap (\((u', v'), w') -> u' (v' w')) ((u ⊗ v) ⊗ w)
```

along with a change of variables

```haskell
> compositionCounterpositive u v w =
>   let
>     pu  = fmap (,) u
>     pv  = fmap (,) v
>     lhs =
>           fmap (\(pu', (pv', w')) -> pu' (pv' w')) (pu ⊗ (pv ⊗ w))
>       === fmap (\(pu', (pv', w')) -> pu' (pv' w')) (fmap (,) u ⊗ (fmap (,) v ⊗ w))
>       --- ...canonicalization steps...
>       === fmap (\(pu', (pv', w')) -> pu' (pv' w')) (fmap ((,) *** ((,) *** id)) (u ⊗ (v ⊗ w)))
>       --- ...canonicalization steps...
>       === fmap (\(u', (v', w')) -> (,) u' ((,) v' (id w'))) (u ⊗ (v ⊗ w))
>       === fmap (\(u', (v', w')) -> (u', (v', w'))) (u ⊗ (v ⊗ w))
>       === fmap id (u ⊗ (v ⊗ w))
>       === u ⊗ (v ⊗ w)
>     rhs =
>           fmap (\((pu', pv'), w') -> pu' (pv' w')) ((pu ⊗ pv) ⊗ w)
>       --- ... same as above up to parenthesis on the arguments---
>       === fmap (\((u', v'), w') -> (u', (v', w'))) ((u ⊗ v) ⊗ w)
>       === fmap assoc ((u ⊗ v) ⊗ w)
>   in
>     lhs === rhs
```

Ok, so we went over associativity and both identities, what about _Homomorphism_ then?
As you might suspect, we don't need it, because it can be derived from the previous laws plus parametricity.

```haskell
> homomorphism :: Applicative f => (a -> b) -> a -> f b
> homomorphism f x =
>       pure f <*> pure x
>   === fmap f (pure x)
>   === (fmap f . pure) x
>   === (pure . f) x
>   === pure (f x)
```

Finally, let's see what the free theorem for `<*>` says

```haskell
(forall h. (forall k p. g . k = p . f => h k = p) => $map h xs = ys) => $map g (xs <*> z) = ys <*> $map f z
```

Er... interpretation left as an exercise for the reader?

Categorical/Compositional formulation
---------------
```haskell
Associativity
  f <.> (g <.> h) = (f <.> g) <.> h

Identities
  f = pure id <.> f
  f = f <.> pure id
```
This is nothing less, nothing more than the [`Control.Category`](https://hackage.haskell.org/package/base/docs/Control-Category.html#t:Category) laws. Or just the [`Data.Semigroupoid`](https://hackage.haskell.org/package/semigroupoids-5.3.7/docs/Data-Semigroupoid.html#t:Semigroupoid) law, if you're only dealing with `Apply`.

Even less well-known than the _Monoidal_ formulation, it's the entire reason this post spawned out of a [github thread](https://github.com/haskell/core-libraries-committee/issues/102#issuecomment-1287693426).
While `<.>` is not used in current pratice, this is as elegant a formulation as we'll get. [@duplode](https://github.com/duplode)'s proofs use equivalence with the `<*>` laws, while here we'll go with `⊗`.

For the identities, we do the usual

```haskell
> leftIdCategorical f =
>       pure id <.> f
>   === liftA2 (.) (pure id) f
>   --- ...canonicalization steps...
>   === fmap (uncurry (.)) (pure id ⊗ f)
>   === fmap (uncurry (.)) (fmap (const id) unit ⊗ fmap id f)
>   === fmap (uncurry (.) . (const id *** id)) (unit ⊗ f)
>   === fmap (\((), f') -> const id () . id f') (unit ⊗ f)
>   === fmap (\((), f') -> f') (unit ⊗ f)
>   === fmap snd (unit ⊗ f)
>   === f

> rightIdCategorical f =
>       f <.> pure id
>   --- same as above but swapped
>   === fmap (\(f', ()) -> id f' . const id ()) (f ⊗ unit)
>   === fmap (\(f', ()) -> f') (f ⊗ unit)
>   === fmap fst (f ⊗ unit)
>   === f
```

For _Associativity_ we mirror what was done for `<*>`

```haskell
> associativityCategorical :: Applicative f => f (c -> d) -> f (b -> c) -> f (a -> b) -> f (a -> d)
> associativityCategorical u v w =
>       u <.> (v <.> w)
>   === liftA2 (.) u (liftA2 (.) v w)
>   === fmap (uncurry (.)) (u ⊗ fmap (uncurry (.)) (v ⊗ w))
>   === fmap (uncurry (.)) (fmap id u ⊗ fmap (uncurry (.)) (v ⊗ w))
>   === fmap (uncurry (.)) (fmap (id *** uncurry (.)) (u ⊗ (v ⊗ w)))
>   === fmap (uncurry (.) . (id *** uncurry (.))) (u ⊗ (v ⊗ w))
>   === fmap (\(u', (v', w')) -> u' . (v' . w')) (u ⊗ (v ⊗ w))
```

The forward direction of the equivalance continues with
```haskell
>   === fmap (\(u', (v', w')) -> u' . (v' . w')) (u ⊗ (v ⊗ w))
>   === fmap (\((u', v'), w') -> u' . (v' . w')) ((u ⊗ v) ⊗ w)
>   === fmap (\((u', v'), w') -> (u' . v') . w') ((u ⊗ v) ⊗ w)
>   === fmap (uncurry (.) . (uncurry (.) *** id)) ((u ⊗ v) ⊗ w)
>   === fmap (uncurry (.)) (fmap (uncurry (.) *** id) ((u ⊗ v) ⊗ w))
>   === fmap (uncurry (.)) (fmap (uncurry (.)) (u ⊗ v) ⊗ fmap id w)
>   === fmap (uncurry (.)) (fmap (uncurry (.)) (u ⊗ v) ⊗ w)
>   === fmap (uncurry (.)) (liftA2 (.) u v ⊗ w)
>   === liftA2 (.) (liftA2 (.) u v) w
>   === liftA2 (.) u v <.> w
>   === (u <.> v) <.> w
```
and to go backwards we take the canonical form again but with an extra `fmap` outside so we can turn the composed function into a triple

```haskell
> associativityCategoricalCanonicalized f u v w =
>       fmap f (fmap (\(u', (v', w')) -> u' . v' . w') (u ⊗ (v ⊗ w)))
>   === fmap f (fmap (\((u', v'), w') -> u' . v' . w') ((u ⊗ v) ⊗ w))
```

and a similar change of variables

```haskell
> associativityCategoricalCounterpositive f u v w =
>   let
>     pu  = fmap (,) u
>     pv  = fmap (,) v
>     pw  = fmap const w
>     lhs =
>           fmap (\(pu', (pv', pw')) -> pu' . pv' . pw') (pu ⊗ (pv ⊗ pw))
>       === fmap (\(pu', (pv', pw')) -> pu' . pv' . pw') (fmap (,) u ⊗ (fmap (,) v ⊗ fmap const w))
>       --- ...canonicalization steps...
>       === fmap (\(u', (v', w')) -> (,) u' . (,) v' . const w') (u ⊗ (v ⊗ w))
>       === fmap (\(u', (v', w')) -> \_ -> (u', (v', w'))) (u ⊗ (v ⊗ w))
>       === fmap const (u ⊗ (v ⊗ w))
>     rhs =
>           fmap (\((pu', pv'), pw') -> pu' . pv' . pw') ((pu ⊗ pv) ⊗ pw)
>       --- ... same as above up to parenthesis on the arguments ...
>       === fmap (\((u', v'), w') -> \_ -> (u', (v', w'))) ((u ⊗ v) ⊗ w)
>       === fmap (const . assoc) ((u ⊗ v) ⊗ w)
>       === fmap const (fmap assoc ((u ⊗ v) ⊗ w))
>   in
>         u ⊗ (v ⊗ w)
>     === fmap (($ ()) . const) (u ⊗ (v ⊗ w))
>     === fmap ($ ()) lhs
>     === fmap ($ ()) rhs
>     === fmap (($ ()) . const . assoc) ((u ⊗ v) ⊗ w)
>     === fmap assoc ((u ⊗ v) ⊗ w)
```

Maybe we can get some more insight by asking lambdabot for the free theorem of (`<.>`) ?


```haskell
   (forall k. (forall p q. g . p = q . f => k p = q) => $map k xs = ys)
=> (forall f1. (forall f2 f3. f . f2 = f3 . h => f1 f2 = f3) => $map f1 zs = us)
=> (forall f5 f6. g . f5 = f6 . h => f4 f5 = f6) => $map f4 (xs <.> zs) = ys <.> us
```

Yikes, let's rename some variables and mess with indentation

```haskell
   (forall k. (forall p q. g . p = q . f => k p = q) => $map k xs = ys)
=> (forall k. (forall p q. f . p = q . h => k p = q) => $map k zs = us)
=>            (forall p q. g . p = q . h => j p = q) => $map j (xs <.> zs) = ys <.> us
```

Ok that looks more workable. If `xs` can be mapped to `ys` by any function that respects certain constraints, and likewise for `zs`/`us`, then under some similar constraints we can also map from one lifted-composition to the other. I guess?

Lifted formulation
---------------
A set of laws based on `liftA2`/`pure` is suggested in https://stackoverflow.com/a/29018816/6276652.
We'll basically adopt the identities

```haskell
f = liftA2 (curry snd) unit f
f = liftA2 (curry fst) f unit
```

but tweak associativity some. We'll require that the lifting operation preserve associativity.

```haskell
let
    f' = liftA2 f
in
    u `f`  (v `f`  w) = (u `f`  v) `f`  w
 => u `f'` (v `f'` w) = (u `f'` v) `f'` w
```

We don't require equivalence since trivial instances can easily invalidate it
```haskell
> instance Apply Proxy where
>   _ <.> _ = Proxy
```

Proving equivalence for the identities is simple

```haskell
> leftIdLifted :: Applicative f => f a -> f a
> leftIdLifted f =
>      liftA2 (curry snd) unit f
>  === fmap (uncurry (curry snd)) (unit ⊗ f)
>  === fmap snd (unit ⊗ f)
>  === f
```

Likewise for right.

Note also these can be rewritten into an alternative pair of identity laws for (`<*>`) that are symmetric, at the cost of longer equations

```haskell
f = curry fst <$> f <*> unit
f = curry snd <$> unit <*> f
```

This associativity law can be proved from the other sets by applying the hypothesis to the canonicalized form

```haskell
> associativityPreserved :: Apply f => (a -> a -> a) -> f a -> f a -> f a -> f a
> associativityPreserved f u v w =
>       liftA2 f u (liftA2 f v w)
>   === fmap (uncurry f) (u ⊗ fmap (uncurry f) (v ⊗ w))
>   === fmap (uncurry f) (fmap id u ⊗ fmap (uncurry f) (v ⊗ w))
>   === fmap (uncurry f) (fmap (id *** uncurry f) (u ⊗ (v ⊗ w)))
>   === fmap (uncurry f . (id *** uncurry f)) (u ⊗ (v ⊗ w))

>   === fmap (\(u', (v', w')) -> f u' (f v' w')) (u ⊗ (v ⊗ w))
>   === fmap (\(u', (v', w')) -> f u' (f v' w')) (fmap assoc ((u ⊗ v) ⊗ w))
>   === fmap (\((u', v'), w') -> f u' (f v' w')) ((u ⊗ v) ⊗ w)
>   === fmap (\((u', v'), w') -> f (f u' v') w') ((u ⊗ v) ⊗ w)

>   === fmap (uncurry f . (uncurry f *** id)) ((u ⊗ v) ⊗ w)
>   === fmap (uncurry f) (fmap (uncurry f *** id) ((u ⊗ v) ⊗ w))
>   === fmap (uncurry f) (fmap (uncurry f) (u ⊗ v) ⊗ fmap id w)
>   === fmap (uncurry f) (fmap (uncurry f) (u ⊗ v) ⊗ w)
>   === liftA2 f (liftA2 f u v) w
```

and since `(.)` is associative, we have

```haskell
> associativityPreservedCounterpositive :: Apply f => f (c -> d) -> f (b -> c) -> f (a -> b) -> f (a -> d)
> associativityPreservedCounterpositive f g h =
>       f <.> (g <.> h)
>   === liftA2 (.) f (liftA2 (.) g h)
>   === liftA2 (.) (liftA2 (.) f g) h
>   === (f <.> g) <.> h
```

Reinforcing this view, the corresponding free theorem seems to also be about preserving a property
```haskell
   (forall x y.     f (       p x y) =        q (    g x) (    h y))
=> (forall x y. map f (liftA2 p x y) = liftA2 q (map g x) (map h y))
```
