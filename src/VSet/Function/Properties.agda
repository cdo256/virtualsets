module VSet.Function.Properties where

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
open import VSet.Function.Iso
open import VSet.Function.Injection


open Iso

private
  variable
    A B C : Type


↔to↣ : (A ↔ B) → (A ↣ B)
↔to↣ f =
  let inj : is-injective (f ^)
      inj x y eq = 
        x
          ≡⟨ sym (cong (λ ○ → ○ x) (linv f)) ⟩
        (f ⁻¹ ∘ f ^) x
          ≡⟨ refl ⟩
        (f ⁻¹) ((f ^) x)
          ≡⟨ cong (f ⁻¹) eq ⟩
        (f ⁻¹) ((f ^) y)
          ≡⟨ refl ⟩
        (f ⁻¹ ∘ f ^) y
          ≡⟨ cong (λ ○ → ○ y) (linv f) ⟩
        y ∎ 
  in f ^ , inj

_↣∘↣_ : (B ↣ C) → (A ↣ B) → (A ↣ C)
(f , inj₁) ↣∘↣ (g , inj₂) = (f ∘ g) , λ x y eq → inj₂ _ _ (inj₁ _ _ eq)

