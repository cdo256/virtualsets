module VSet.Function.Injection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Core.Primitives

is-injective : {X Y : Type} → (f : X → Y) → Type
is-injective {X} f = ∀ (x y : X) → f x ≡ f y → x ≡ y

_↣_ : (X Y : Type) → Type
X ↣ Y = Σ (X → Y) is-injective

↣-id : (X : Type) → X ↣ X
↣-id X = (λ x → x) , (λ x y p → p)

transport-inj
  : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : A ≡ B)
  → transport p x ≡ transport p y
  → x ≡ y
transport-inj {x = x} {y = y} p q =
  x ≡⟨ sym (transport⁻Transport p x) ⟩
  transport (sym p) (transport p x) ≡⟨ cong (transport (sym p)) q ⟩
  transport (sym p) (transport p y) ≡⟨ transport⁻Transport p y ⟩
  y ∎

