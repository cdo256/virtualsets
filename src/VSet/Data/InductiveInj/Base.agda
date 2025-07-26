module VSet.Data.InductiveInj.Base where

open import VSet.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import Cubical.Data.List.Base

private
  variable
    m n : ℕ

data Inj : ℕ → ℕ → Type where
  nul : ∀ n → Inj 0 n
  inc : ∀ {m n} → (b : Fin (suc n))
      → (inj : Inj m n)
      → Inj (suc m) (suc n)

inc-bigger : ∀ {n} → (b : Fin (suc n)) → (a : Fin n) → Fin (suc n)
inc-bigger fzero a = fsuc a
inc-bigger (fsuc b) fzero = fzero
inc-bigger (fsuc b) (fsuc a) = fsuc (inc-bigger b a)

apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc b inj) fzero = b
apply (inc b inj) (fsuc a) =
  inc-bigger b (apply inj a)

