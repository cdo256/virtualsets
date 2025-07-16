module VSet.Function.Properties where

open import VSet.Path
open import VSet.Prelude
open import VSet.Data.Sum.Properties
open import VSet.Function.Iso
open import VSet.Function.Injection

open Iso

private
  variable
    A B C D : Type


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

infixl 5 _↣∘↣_

_↣∘↣_ : (B ↣ C) → (A ↣ B) → (A ↣ C)
(f , inj₁) ↣∘↣ (g , inj₂) = (f ∘ g) , λ x y eq → inj₂ _ _ (inj₁ _ _ eq)

↣-map-⊎ : {A B C D : Type ℓ-zero} → (A ↣ B) → (C ↣ D) → ((A ⊎ C) ↣ (B ⊎ D)) 
↣-map-⊎ {A} {B} {C} {D} f g = h , inj
  where
    h : (A ⊎ C) → (B ⊎ D)
    h = ⊎-map (fst f) (fst g)

    inj : (x y : A ⊎ C) → h x ≡ h y → x ≡ y
    inj (inl a₁) (inl a₂) hx≡hy =
        cong inl
      $ snd f a₁ a₂
      $ inl-injective (fst f a₁) (fst f a₂)
      $ hx≡hy
    inj (inl a₁) (inr c₂) hx≡hy =
      absurd (inl≢inr (fst f a₁) (fst g c₂) hx≡hy)
    inj (inr c₁) (inl a₂) hx≡hy =
      absurd (inl≢inr (fst f a₂) (fst g c₁) (sym hx≡hy))
    inj (inr c₁) (inr c₂) hx≡hy =
        cong inr
      $ snd g c₁ c₂
      $ inr-injective (fst g c₁) (fst g c₂)
      $ hx≡hy
