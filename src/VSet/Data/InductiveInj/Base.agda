module VSet.Data.InductiveInj.Base where

open import VSet.Prelude
open import Cubical.Data.Prod.Base hiding (map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import Cubical.Data.List.Base hiding ([_])

private
  variable
    m n : ℕ

data Inj : ℕ → ℕ → Type where
  nul : ∀ n → Inj 0 n
  inc : ∀ {m n} → (b : Fin (suc n))
      → (inj : Inj m n)
      → Inj (suc m) (suc n)

Injsuc : ℕ → ℕ → Type
Injsuc m n = Inj (suc m) (suc n)

apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc b inj) fzero = b
apply (inc b inj) (fsuc a) =
  fsplice b (apply inj a)

to-list : Inj m n → List (Fin n)
to-list (nul _) = []
to-list (inc b f) =
  b ∷ map (fsplice b) (to-list f)

idInj : ∀ m → Inj m m
idInj zero = nul zero
idInj (suc m) = inc fzero (idInj m)

cross : Inj 2 2
cross = inc (fsuc fzero) $ inc fzero $ nul 0

-- eg. cycle-l 5 = (5 0 1 2 3 4)
cycle-l : ∀ m → Inj (suc m) (suc m)
cycle-l m = inc fmax (idInj m)

-- eg. cycle-r 5 = (1 2 3 4 5 0)
cycle-r : ∀ m → Inj (suc m) (suc m)
cycle-r zero = idInj 1
cycle-r (suc m) = inc (fsuc fzero) (cycle-r m)

c1 = to-list (cycle-r 3)
c2 = to-list (cycle-l 3)
