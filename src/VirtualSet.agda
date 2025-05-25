module VirtualSet {ℓ} where

open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional
open import Data.Product

AllIn : (A : Set) → (xs : List A) → Set
AllIn A xs = ∀ (a : A) → a ∈ xs

FiniteSet : (A : Set) → Set
FiniteSet A = Σ[ xs ∈ List A ] AllIn A xs
-- FiniteSet A = Σ[ xs ∈ List A ] ∀[ a ∈ A ] ( ) 
-- FiniteSet A = Σ[ n ∈ ℕ ] (Σ[ f ∈ (Fin n → A) ] (Π[ a ∈ A ] (Σ[ i ∈ Fin n ] ( a ≡ f i ))))
