module VirtualSet.Iso where

open import 1Lab.Type
  using (Type; Typeω; ⊥; absurd; _×_; _,_; ¬_; _∘_; id)
open import 1Lab.Path using (refl; sym; ap; subst; _≡_; funext)
open import 1Lab.Equiv
  using (iso; Iso; is-iso; is-right-inverse; is-left-inverse;
         _≃_)
open import Prim.Data.Sigma
  using (Σ; Σ-syntax; fst; snd)

infix 1 _↔_

_↔_ : (A B : Type) → Type
A ↔ B = Iso A B

module _ {A B : Type} where
  infix 90 _^ _⁻¹

  _^  : (A↔B : A ↔ B) → A → B
  A↔B ^ = fst A↔B
  _⁻¹ : (A↔B : A ↔ B) → B → A
  A↔B ⁻¹ = is-iso.from (snd A↔B)

  rinv : (A↔B : A ↔ B) → A↔B ^ ∘ A↔B ⁻¹ ≡ id
  rinv A↔B = funext (is-iso.rinv (snd A↔B))
  linv : (A↔B : A ↔ B) → A↔B ⁻¹ ∘ A↔B ^ ≡ id
  linv A↔B = funext (is-iso.linv (snd A↔B))
