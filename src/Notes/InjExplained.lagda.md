```
module Notes.InjExplained where

open import VSet.Prelude
open import Cubical.Data.Nat.Base
open import VSet.Data.Fin.Base
open import VSet.Function.Injection
```

I have taken the approach of using a basic inductive definition for
injective functions. This was because the previous way of doing it was
messy, and ultimately hid the true behaviour that I wanted to extract
with a trace. This meant that all of the proofs relied on a long chain
of isomorphisms that weren't strong enough to capture the behaviour
that we cared about, namely adding and removing links to modify a
funciton.

Additionally carrying around the proof meant they had to be modified
together, and may have been the reason I was experiencing performance
reduction when type checking Agda.

I noticed that I wasn't getting the benefit I expected from all of
these abstractions and that ultimately proving these isomorphisms were
distracting from the main aim which is ensure that a trace structure
is formed from Virtual Sets. I do think this method could have worked
if I had enough time, but the problem is that I didn't have the time
to spare. Additionally techniques I've learnt made it clear that
there were much better ways of structuring things so that . (?)

In the aid of this simplicity, I decided to switch to the following
structure to represent injective Fin funcitons:

```
data Inj : ℕ → ℕ → Type where
  nul : ∀ n → Inj 0 n
  inc : ∀ {m n} → (b : Fin (suc n))
      → (inj : Inj m n)
      → Inj (suc m) (suc n)
```

This replaces the previous definition:

```
[_↣_] : ℕ → ℕ → Type
[ X ↣ Y ] = Σ (Fin X → Fin Y) is-injective
```

The way it works is that nul introduces an empty function from `Fin 0`
to some `Fin n`. Then each subsequent `inc` adds a single link
shifting the domain and codomain such that it is impossible to
construct a non-injective function.

I represent these functions as vectors of finite values, where the
position corresponds to each domain element, and the number is what that
element is mapped to. For example,

```txt
  (1 2 0)
```

maps 0 to 1, 1 to 2, and 2 to 0. Note that there is some ambiguity
with this notation in that we haven't specified the size of the
codomain. Strictly we would want to specify the type to fully specify
this.

In our notation we would represent this as:

```
f : Inj 3 3
f = inc f1 $ inc f1 $ inc f0 $ nul 0
```

This is read right to left. First we start with `nul 0` which is an
empty function with an empty codomain. The difference between the size
of the domain and the codomain is specified entirely by this nul
funciton. Starting with `nul 0` means we will end up with a bijection,
although this needs to be proven.

Next we add a single link from f0 to f0. This is the only choice we
have at this stage because we're creating a function from Fin 1 to Fin
1 from `nul 0 : Fin 0 → Fin 0`.

The second link we add gives us two choices. We can either be parallel
to the first link or cross over it. `(inc f0 $ inc f0 $ nul 0)` is two
parallel links. `(inc f1 $ inc f0 $ nul 0)` is two crossing
links. Note that these are the only two bijections from Fin 2 to Fin 2
available. We choose to cross in this example.

Finally the third link can either cross over both (`f2`), cross over just
one (`f1`), or not cross at all (`f0`). We choose the middle option
and end up with a cycle. Note that after nul 0, we three choices, 1 *
2 * 3 = 3!. Every inc that is added increases the type of the Fin
added by 1. There fore, starting with `nul 0` to make Inj m m, there
are m! options, which indicates that we're representing all
possibilities. (Though it still needs to be checked that there is only
one way to construct each function.)

This has the nice properties that all constructions are necessarily
injective, since it is impossible to constrct two outputs that are the
same, for example (0 0) : Fin 2 cannot be constructed.


