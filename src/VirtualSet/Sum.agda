module VirtualSet.Sum where

open import 1Lab.Equiv using (iso; Iso; is-right-inverse; is-left-inverse)
open import 1Lab.HIT.Truncation using (∃)
open import 1Lab.Path
open import 1Lab.Type
open import 1Lab.Univalence
open import Data.Dec
open import Data.Fin
open import Data.Irr
open import Data.Nat.Base
  using (Nat; suc-inj; zero; suc; _<_; _≤_; ≤-trans; s≤s; s≤s')
  renaming (_+_ to _+ℕ_)
open import Data.Nat.Order
open import Data.Nat.Properties
open import Data.Sum
open import Meta.Idiom
open import Prim.Data.Sigma
  using (Σ; Σ-syntax; fst; snd)


⊎-swap : ∀ {X Y : Type} → (X ⊎ Y) → (Y ⊎ X)
⊎-swap {X} {Y} (inl x) = inr x
⊎-swap {X} {Y} (inr x) = inl x

⊎-swap-↔ : ∀ {X Y : Type} → Iso (X ⊎ Y) (Y ⊎ X)
⊎-swap-↔ = ⊎-swap , iso ⊎-swap swap2 swap2
  where
    swap2 : ∀ {X Y : Type} → (z : X ⊎ Y) → ⊎-swap (⊎-swap z) ≡ z
    swap2 (inl x) = refl
    swap2 (inr x) = refl
