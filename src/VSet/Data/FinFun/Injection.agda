module VSet.Data.FinFun.Injection where

open import Cubical.Data.Nat.Properties

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties


[_↣_] : ℕ → ℕ → Type
[ X ↣ Y ] = ⟦ X ⟧ ↣ ⟦ Y ⟧

id↣ : ∀ {A} → A ↣ A
id↣ {A} = id , λ x y z → z

FinFun : ∀ (A B : ℕ) → Type
FinFun A B = Fin A → Fin B

FinFun' : ℕ × ℕ → Type
FinFun' (A , B) = FinFun A B

