module VirtualSet.Order where

open import 1Lab.Equiv using (iso; Iso; is-right-inverse; is-left-inverse)
open import 1Lab.HIT.Truncation using (∃)
open import 1Lab.Path
open import 1Lab.Type
open import 1Lab.Univalence
open import Data.Dec
open import Data.Fin
  renaming (_<_ to _<ꟳ_; _≤_ to _≤ꟳ_; zero to vzero; suc to vsuc)
open import Data.Irr
open import Data.Nat.Base
  renaming (_+_ to _+ℕ_)
open import Data.Nat.Order
open import Data.Nat.Properties
open import Data.Sum
open import Meta.Idiom
open import Prim.Data.Sigma
  using (Σ; Σ-syntax; fst; snd)

open import VirtualSet.Iso

open _≤_

<→≤ : ∀ {x y : Nat} → x < suc y → x ≤ y 
<→≤ {x} {y} x<sy with inspect x<sy
... | sx≤sy , eq = ≤-peel sx≤sy

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = ¬ x ≡ y

_≤?_ : (x y : Nat) → Dec (x ≤ y)
zero ≤? y = yes 0≤x
suc x ≤? zero = no (λ ())
suc x ≤? suc y with x ≤? y
... | yes x≤y = yes (s≤s x≤y)
... | no x≰y = no (λ sx≤sy → x≰y (≤-peel sx≤sy))

_<?_ : (x y : Nat) → Dec (x < y)
x <? y = suc x ≤? y

_≤ꟳ?_ : ∀ {x y : Nat} → (a b : Fin x) → Dec (a ≤ꟳ b)
fin a ≤ꟳ? fin b = a ≤? b

_<ꟳ?_ : ∀ {x y : Nat} → (a b : Fin x) → Dec (a <ꟳ b)
fin a <ꟳ? fin b = a <? b
