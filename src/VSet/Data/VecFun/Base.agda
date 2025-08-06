module VSet.Data.VecFun.Base where

open import VSet.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec hiding (lookup)
open import VSet.Data.Fin.Base

VecFun : (m n : ℕ) → Type
VecFun m n = Vec (Fin n) m 

lookup : {m n : ℕ} → VecFun m n → Fin m → Fin n
lookup (b ∷ _) fzero = b
lookup (_ ∷ f) (fsuc a) = lookup f a

isInjective : {m n : ℕ} → VecFun m n → Type
isInjective {m} {n} f = (a b : Fin m) → lookup f a ≡ lookup f b → a ≡ b

VecInj : (m n : ℕ) → Type
VecInj m n = Σ (VecFun m n) isInjective
