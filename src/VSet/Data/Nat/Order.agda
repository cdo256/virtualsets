module VSet.Data.Nat.Order where

open import VSet.Prelude

open import Cubical.Data.Nat 
open import Cubical.Data.Nat.Order.Inductive public
  renaming (_<ᵗ_ to _<_)

private
  variable
    ℓ : Level

¬-<-zero : ∀ {x : ℕ} → ¬ x < zero
¬-<-zero {x} x<0 = x<0

pred-<-pred : ∀ {m n : ℕ} → suc m < suc n → m < n 
pred-<-pred {zero} {suc n} sm<sn = tt
pred-<-pred {suc m} {n} sm<sn = sm<sn

suc-<-suc : ∀ {m n : ℕ} → m < n → suc m < suc n
suc-<-suc {m} {n} m<n = m<n
