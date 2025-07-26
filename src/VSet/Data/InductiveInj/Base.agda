module VSet.Data.InductiveInj.Base where

open import VSet.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import VSet.Data.Fin.Base

private
  variable
    m n : ℕ

data Inj : ℕ → ℕ → Type where
  nul : ∀ n → Inj 0 n
  inc : ∀ m n → (b : Fin (suc n))
              → (inj : Inj m n)
              → Inj (suc m) (suc n)

inj-insert : ∀ {n} → (b : Fin n) → (b' : Fin (suc n))
           → Singleton (fsuc b ≟ᶠ b') → Fin (suc n) 
inj-insert b b' (tri , eq;) = {!!}

apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc m n b inj) fzero = b
apply (inc m n b' inj) (fsuc a) =
  let b = apply inj a
  in {!apply-inc (suc b ≟ b')!}
  
