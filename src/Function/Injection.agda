module VirtualSet.Injection where

open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
open import Prim.Data.Sigma

is-injective : {X Y : Type} → (f : X → Y) → Type
is-injective {X} f = ∀ (x y : X) → f x ≡ f y → x ≡ y

_↣_ : (X Y : Type) → Type
X ↣ Y = Σ (X → Y) is-injective

Injection : (X Y : Type) → Type
Injection X Y = X ↣ Y
Injective : {X Y : Type} → (f : X → Y) → Type
Injective f = is-injective f
