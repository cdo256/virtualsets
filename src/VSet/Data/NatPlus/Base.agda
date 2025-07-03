module VSet.Data.NatPlus.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives

open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ

open import VSet.Path

data ℕ+ : Type where
  one : ℕ+
  suc : ℕ+ → ℕ+

ℕ+→ℕ : ℕ+ → ℕ
ℕ+→ℕ one = 1
ℕ+→ℕ (suc x) = ℕ.suc (ℕ+→ℕ x)

ℕ→ℕ+ : (x : ℕ) → x ≢ ℕ.zero → ℕ+
ℕ→ℕ+ ℕ.zero ne = absurd (ne refl)
ℕ→ℕ+ (ℕ.suc ℕ.zero) _ = one
ℕ→ℕ+ (ℕ.suc (ℕ.suc x)) _ = {!suc (ℕ→ℕ+ (ℕ.suc x) ?)!}

_+_ : ℕ+ → ℕ+ → ℕ+
one + y = suc y
suc x + y = suc (x + y)
