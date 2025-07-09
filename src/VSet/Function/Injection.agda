module VSet.Function.Injection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

is-injective : {X Y : Type} → (f : X → Y) → Type
is-injective {X} f = ∀ (x y : X) → f x ≡ f y → x ≡ y

_↣_ : (X Y : Type) → Type
X ↣ Y = Σ (X → Y) is-injective

↣-id : (X : Type) → X ↣ X
↣-id X = (λ x → x) , (λ x y p → p)

Injection : (X Y : Type) → Type
Injection X Y = X ↣ Y
Injective : {X Y : Type} → (f : X → Y) → Type
Injective f = is-injective f
