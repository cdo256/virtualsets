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

This allows you to access the variables in the where clause as if it were a module-- because it is!!
