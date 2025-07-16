module VSet.Transform.Tensor where

open import VSet.Prelude
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import Cubical.Data.Nat.Properties

open import VSet.Data.Nat using (ℕ; zero; suc)
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Data.SomeFin.Properties
open import VSet.Transform.Split using (⊎↔+)
open import VSet.Transform.Pred

tensor : ∀ {W X Y Z : SomeFin} → [ W ↣ X ] → [ Y ↣ Z ] → [ W + Y ↣ X + Z ]
tensor {W} {X} {Y} {Z} f g = ↔to↣ ⊎↔+ ↣∘↣ ↣-map-⊎ f g ↣∘↣ ↔to↣ (flip-↔ ⊎↔+)

𝟘 : [ 0 ↣ 0 ]
𝟘 = ↣-id ⟦ 0 ⟧

infixl 30 _⊕_

_⊕_ : ∀ {W X Y Z : SomeFin} → [ W ↣ X ] → [ Y ↣ Z ] → [ W + Y ↣ X + Z ]
f ⊕ g = tensor f g

ladd : ∀ {X Y : SomeFin} → (A : SomeFin) → [ X ↣ Y ] → [ A + X ↣ A + Y ]
ladd {X} {Y} A f = (↣-id ⟦ A ⟧) ⊕ f

radd : ∀ {X Y : SomeFin} → (A : SomeFin) → [ X ↣ Y ] → [ X + A ↣ Y + A ]
radd {X} {Y} A f = f ⊕ (↣-id ⟦ A ⟧)
