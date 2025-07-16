module VSet.Data.SomeFin.Injection where

open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base


[_↣_] : SomeFin → SomeFin → Type
[ X ↣ Y ] = ⟦ X ⟧ ↣ ⟦ Y ⟧

id↣ : ∀ {A} → A ↣ A
id↣ {A} = id , λ x y z → z

FinFun : ∀ (A B : ℕ) → Type
FinFun A B = Fin A → Fin B
