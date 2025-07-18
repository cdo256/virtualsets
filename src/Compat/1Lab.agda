module Compat.1Lab where

open import Cubical.Foundations.Prelude renaming (hcomp to cubical-hcomp)
-- open import Cubical.Foundations.Function 
-- open import Cubical.Foundations.Transport hiding (transpEquiv)
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Core.Primitives 

-- open import Cubical.Data.Empty public renaming (elim to absurd)
-- open import Cubical.Data.Unit.Base public renaming (Unit to ⊤)
-- open import Cubical.Relation.Nullary public
-- open import Cubical.Data.Sum public
--   renaming (rec to ⊎-rec; elim to ⊎-elim; map to ⊎-map)

hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
hcomp {A = A} φ u = X.primHComp sys (u i0 1=1) module hcomp-sys where
  sys : ∀ j → Partial φ A
  sys j (φ = i1) = u j 1=1

hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u = hcomp (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1

doubleHComp : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → w ≡ x → x ≡ y → y ≡ z
            → w ≡ z
doubleHComp p q r i = hcomp (λ j _ → {!!}) {!!} {!!}
