module VirtualSet.Interval where

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

between  : Nat → Nat → Nat → Type
between l u x = l ≤ x × x < u

record Interval (l u : Nat) : Type where
  constructor interval
  field
    lower : Nat
    ⦃ bounded ⦄ : Irr (between l u lower)

rshift-interval : {u l x : Nat} → Interval l u → Interval (x + l) (x + u)
fin→interval : {x : Nat} → Fin x → Interval 0 x
fin→interval (fin a ⦃ a<x ⦄) = interval a ⦃ (λ ○ → 0≤x , ○) <$> a<x ⦄
interval→fin : {x y : Nat} → Interval x y → Fin y
