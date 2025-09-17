module VSet.Transform.InjFun.Compose where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.InjFun.Injection
open import VSet.Transform.InjFun.Pred

infixl 10 _∘ʲ_

_∘ʲ_ : ∀ {X Y Z} → [ Y ↣ Z ] → [ X ↣ Y ] → [ X ↣ Z ]
_∘ʲ_ g f = (fst g ∘ fst f) , λ x y z → f .snd x y (g .snd (f .fst x) (f .fst y) z)

-- Reverse composition
_∘⁻ʲ_ : ∀ {X Y Z} → [ X ↣ Y ] → [ Y ↣ Z ] → [ X ↣ Z ]
f ∘⁻ʲ g = g ∘ʲ f

Id : ∀ {X} → [ X ↣ X ]
Id = (λ x → x) , λ x y eq' → eq'

∘ʲ-IdR : {X Y : ℕ} (f : [ X ↣ Y ]) → (f ∘ʲ Id) ≡ f
∘ʲ-IdR f = refl

∘ʲ-IdL : {X Y : ℕ} (f : [ X ↣ Y ]) → (Id ∘ʲ f) ≡ f
∘ʲ-IdL f = refl
