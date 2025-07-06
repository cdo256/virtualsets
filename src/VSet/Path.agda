module VSet.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path public
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)


private
  variable
    ℓ : Level


_≢_ : ∀ {ℓ} {A : Type ℓ} → (x y : A) → Type ℓ
x ≢ y = x ≡ y → ⊥

≢sym : {A : Type ℓ} {x y : A} → (x ≢ y) → (y ≢ x)
≢sym x≢y y≡x = x≢y (sym y≡x)

≢cong : ∀ {A B : Type} {x y : A} (f : A → B) → f x ≢ f y → x ≢ y
≢cong {A} {B} {x} {y} f fx≢fy x≡y = fx≢fy (cong f x≡y)
