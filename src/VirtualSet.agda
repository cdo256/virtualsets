module VirtualSet where

open import Data.Nat
  hiding (_⊔_)
open import Data.Fin
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional
open import Data.Product
open import Relation.Binary.Bundles
open import Level
  using (_⊔_; 0ℓ)
  renaming (suc to lsuc)

private
  variable
    ℓ : Level.Level

AllIn : (A : Set ℓ) → (xs : List A) → Set ℓ
AllIn A xs = ∀ (a : A) → a ∈ xs

IsFinite : (A : Set ℓ) → Set ℓ
IsFinite A = Σ[ xs ∈ List A ] AllIn A xs

record FiniteSetoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ
    isFinite : IsFinite (Setoid.Carrier setoid)

emptySetoid : Setoid 0ℓ 0ℓ
emptySetoid = Setoid
  { Carrier = ⊥
  -- ; _≈_ = (λ x y → ⊥)
  -- ; isEquivalence = ?
  }
