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


≅to↣ : (A ≅ B) → (A ↣ B)
≅to↣ f =
  let inj : is-injective (fun f)
      inj x y eq = 
        x
          ≡⟨ sym (cong (λ ○ → ○ x) (linv f)) ⟩
        (inv f ∘ fun f) x
          ≡⟨ refl ⟩
        inv f (fun f x)
          ≡⟨ cong (inv f) eq ⟩
        inv f (fun f y)
          ≡⟨ refl ⟩
        (inv f ∘ fun f) y
          ≡⟨ cong (λ ○ → ○ y) (linv f) ⟩
        y ▯ 
  in fun f , inj

≡to↣ : ∀ {A B} → A ≡ B → A ↣ B
≡to↣ p = transport p , λ x y q → transport-inj p q

refl-to-↣-is-id : ∀ {A} → fst (≡to↣ (refl {x = A})) ≡ id
refl-to-↣-is-id =
  funExt (λ x →
    fst (≡to↣ refl) x ≡⟨ refl ⟩
    transport refl x ≡⟨ transportRefl x ⟩
    x ▯)

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

↣∘↣-idR : ∀ {X Y : Type} (f : X ↣ Y) → f ↣∘↣ ↣-id X ≡ f
↣∘↣-idR (f , f-inj) = refl

↣∘↣-idL : ∀ {X Y : Type} (f : X ↣ Y) → ↣-id Y ↣∘↣ f ≡ f
↣∘↣-idL (f , f-inj) = refl

↣∘↣-assoc : ∀ {A B C D : Type} (h : C ↣ D) (g : B ↣ C) (f : A ↣ B)
          → h ↣∘↣ (g ↣∘↣ f) ≡ (h ↣∘↣ g) ↣∘↣ f
↣∘↣-assoc h g f = refl

id≡transport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
             → (λ i → A → p i) [ id ≡ transport p ]
id≡transport p = funExt (transport-filler p)

id≡subst : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} 
        → (B : A → Type ℓ') (p : x ≡ y)
        → (λ i → B x → B (p i)) [ id ≡ subst B p ]
id≡subst B p = funExt (subst-filler B p) 

id≡subst' : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} 
        → (B : A → Type ℓ') (p : x ≡ y)
        → (λ i → B (p i) → B x) [ id ≡ subst B (sym p) ]
id≡subst' B p = {!subst-filler B ?!} 
