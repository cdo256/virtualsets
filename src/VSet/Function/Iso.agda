module VSet.Function.Iso where

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

open import VSet.Path
open import VSet.Function.Base

open Iso

private
  variable
    A B C D : Type

infix 1 _↔_

_↔_ : (A B : Type) → Type
A ↔ B = Iso A B

module _ {A B : Type} where
  infix 90 _^ _⁻¹

  _^  : (A↔B : A ↔ B) → A → B
  A↔B ^ = fun A↔B
  _⁻¹ : (A↔B : A ↔ B) → B → A
  A↔B ⁻¹ = inv A↔B

  rinv : (A↔B : A ↔ B) → A↔B ^ ∘ A↔B ⁻¹ ≡ id
  rinv A↔B = funExt (rightInv A↔B)
  linv : (A↔B : A ↔ B) → A↔B ⁻¹ ∘ A↔B ^ ≡ id
  linv A↔B = funExt (leftInv A↔B)

mkIso : {A B : Type}
      → (f : A → B) → (g : B → A)
      → f ∘ g ≡ id → g ∘ f ≡ id
      → Iso A B
mkIso {A} {B} f g ri li =
  iso f g r l
  where
    l : (a : A) → g (f a) ≡ a
    l a = cong (λ ○ → ○ a) li
    r : (b : B) → f (g b) ≡ b
    r b = cong (λ ○ → ○ b) ri

flip-↔ : (A ↔ B) → (B ↔ A)
flip-↔ A↔B = invIso A↔B

infixl 9 _↔∘↔_

_↔∘↔_ : (B ↔ C) → (A ↔ B) → (A ↔ C)
g ↔∘↔ f = compIso f g

module _ where
  double-flip : ∀ {A B} (R : A ↔ B) → (flip-↔ {B} {A} (flip-↔ {A} {B} R)) ≡ R
  double-flip R i .fun = fun R
  double-flip R i .inv = inv R
  double-flip R i .rightInv = rightInv R
  double-flip R i .leftInv = leftInv R
  
  flip-IsId : ∀ {A B} (R : A ↔ B) → ((flip-↔ R) ↔∘↔ R) ^ ≡ id
  flip-IsId R i x = leftInv R x i
