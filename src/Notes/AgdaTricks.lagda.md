```
module Notes.AgdaTricks where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Cubical.Core.Primitives

Set : Type₁
Set = Type
```

# Well-founded recursion

https://armkeh.github.io/blog/WellFoundedRecursion.html

'rs` is an example of an object where for all smaller x. we can recurse smaller.

```
WfRec : {A : Type} → (A → A → Type) → (A → Type) → A → Type
WfRec {A} _<_ P x = {y : A} → y < x → P y
```

```
data Acc {A : Type} (_<_ : A → A → Type) (x : A) : Type where
  acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x

Well-founded : {A : Type} → (A → A → Type) → Type
Well-founded {A} _<_ = (x : A) → Acc _<_ x
```

You can use modules as 'where' clauses. See this example from 1Lab.

```agda
1lab-hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
1lab-hcomp {A = A} φ u = hcomp sys (u i0 1=1) module hcomp-sys where
  sys : ∀ j → Partial φ A
  sys j (φ = i1) = u j 1=1
```

This allows you to access the variables in the where clause as if it
were a module-- because it is!!

## Write your main definitions, simplify them, then write them again

In most programming languages, the only thing that matters about a
funciton you write is its type and its behaviour. You have probably
read that Agda and other dependently typed langauges are
*proof-relevant*. This means that if you write a definition or central
proof/construciton, then every property you prove about it will
rely on this term. This means that changing the term even a little can
result in proofs breaking and often require substantial modification
to correct.

The takeaway is that if you write a term in Agda that you expect will
be used multiple times, then making the definitions as short as
possible helps a lot.

## Avoid `with` clauses in definitions

`with` clauses are a convenient way to expand with extra patterns
derived from terms computed when matching cases. Unfortunately it
originates from the depths of hell and will destory your ability to
reason about your programs. Here are 3 more *reasonable* definitions
you can use instead:

1. Use case_of_ which has better ability to reason about your code,
even if the syntax is a bit rough around the edges.
2. Use a helper funciton in a where clause.
3. Use a global helper funciton to peform the secondary matching.

## 
