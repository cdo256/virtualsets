module VSet.Data.NatPlus.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ

data ℕ+ : Type where
  one : ℕ+
  suc : ℕ+ → ℕ+

ℕ+→ℕ : ℕ+ → ℕ
ℕ+→ℕ one = 1
ℕ+→ℕ (suc x) = ℕ.suc (ℕ+→ℕ x)

_+_ : ℕ+ → ℕ+ → ℕ+
one + y = suc y
suc x + y = suc (x + y)
