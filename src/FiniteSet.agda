module FiniteSet where

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

module _ (A : Set ℓ) where
  AllIn : (xs : List A) → Set ℓ
  AllIn xs = ∀ (a : A) → a ∈ xs
  
  IsFinite : Set ℓ
  IsFinite = Σ[ xs ∈ List A ] AllIn xs

record FiniteSet ℓ : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    isFinite : IsFinite Carrier

emptyFiniteSet : FiniteSet 0ℓ 
emptyFiniteSet = record
  { Carrier = ⊥
  ; isFinite = [] , λ ()
  }
