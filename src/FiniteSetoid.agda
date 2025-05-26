module FiniteSetoid where

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
open import Data.Empty

private
  variable
    c ℓ : Level.Level


module _ (S : Setoid c ℓ) where
  open Setoid S
    renaming (Carrier to A)

  AllIn : (xs : List (Setoid.Carrier S)) → Set (c ⊔ ℓ)
  AllIn xs = ∀ (a : A) → Σ[ b ∈ A ] a ≈ b × b ∈ xs 

  IsFiniteSetoid : Set (c ⊔ ℓ) 
  IsFiniteSetoid =  Σ[ xs ∈ List A ] AllIn xs

record FiniteSetoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ
    isFinite : IsFiniteSetoid setoid 

emptySetoid : Setoid 0ℓ 0ℓ
emptySetoid = record
  { Carrier = ⊥
  ; _≈_ = _
  ; isEquivalence =  _
  }

emptyFiniteSetoid : FiniteSetoid 0ℓ 0ℓ
emptyFiniteSetoid = record
  { setoid = emptySetoid
  ; isFinite = [] , λ () 
  }
