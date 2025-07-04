module VSet.Data.SomeFin.Injection where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Fin.Default
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base

infixl 8 _+ᶠ_ _-ᶠ_

[_↣_] : SomeFin → SomeFin → Type
[ X ↣ Y ] = ⟦ X ⟧ ↣ ⟦ Y ⟧

id↣ : ∀ {A} → A ↣ A
id↣ {A} = id , λ x y z → z

