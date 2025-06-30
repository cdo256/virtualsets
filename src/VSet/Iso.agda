module VirtualSet.Iso where

open import 1Lab.Type
open import 1Lab.Path
open import 1Lab.Equiv
open import Prim.Data.Sigma

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

∘-assoc : ∀ {A B C D} (h : C → D) (g : B → C) (f : A → B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc h g f = refl

id-r : ∀ {A B} (f : A → B)
     → f ∘ id ≡ f
id-r f = refl

id-l : ∀ {A B} (f : A → B)
     → id ∘ f ≡ f
id-l f = refl

mkIso : {A B : Type}
      → (f : A → B) → (g : B → A)
      → f ∘ g ≡ id → g ∘ f ≡ id
      → Iso A B
mkIso f g ri li =
  f , (iso g 
      (λ b → 
        f (g b) ≡⟨ refl ⟩
        (f ∘ g) b ≡⟨ ap (λ ○ → ○ b) ri ⟩
        id b ≡⟨ refl ⟩
        b ∎)
      (λ a → 
        g (f a) ≡⟨ refl ⟩
        (g ∘ f) a ≡⟨ ap (λ ○ → ○ a) li ⟩
        id a ≡⟨ refl ⟩
        a ∎))



module _ {A B C D : Type} where
  flip-↔ : (A ↔ B) → (B ↔ A)
  flip-↔ A↔B = mkIso (A↔B ⁻¹) (A↔B ^) (linv A↔B) (rinv A↔B)

  infixl 9 _↔∘↔_ _↣∘↣_

  _↔∘↔_ : (B ↔ C) → (A ↔ B) → (A ↔ C)
  g ↔∘↔ f =
    let fg-rinv : (g ^ ∘ f ^) ∘ (f ⁻¹ ∘ g ⁻¹) ≡ id
        fg-rinv =
          (g ^ ∘ f ^) ∘ (f ⁻¹ ∘ g ⁻¹)
            ≡⟨ sym (∘-assoc (g ^) (f ^) (f ⁻¹ ∘ g ⁻¹)) ⟩
          g ^ ∘ (f ^ ∘ (f ⁻¹ ∘ g ⁻¹))
            ≡⟨ ap (g ^ ∘_) (∘-assoc (f ^) (f ⁻¹) (g ⁻¹)) ⟩
          g ^ ∘ ((f ^ ∘ f ⁻¹) ∘ g ⁻¹)
            ≡⟨ ap (λ ○ → g ^ ∘ (○ ∘ g ⁻¹)) (rinv f) ⟩
          g ^ ∘ (id ∘ g ⁻¹)
            ≡⟨ ap (λ ○ → (g ^) ∘ ○) (id-l (g ⁻¹)) ⟩
          g ^ ∘ g ⁻¹
            ≡⟨ rinv g ⟩
          id ∎
        fg-linv : (f ⁻¹ ∘ g ⁻¹) ∘ (g ^ ∘ f ^) ≡ id
        fg-linv =
          (f ⁻¹ ∘ g ⁻¹) ∘ (g ^ ∘ f ^)
            ≡⟨ sym (∘-assoc (f ⁻¹) (g ⁻¹) (g ^ ∘ f ^)) ⟩
          f ⁻¹ ∘ (g ⁻¹ ∘ (g ^ ∘ f ^))
            ≡⟨ ap (λ ○ → f ⁻¹ ∘ ○) (∘-assoc (g ⁻¹) (g ^) (f ^)) ⟩
          f ⁻¹ ∘ ((g ⁻¹ ∘ g ^) ∘ f ^)
            ≡⟨ ap (λ ○ → f ⁻¹ ∘ (○ ∘ f ^)) (linv g) ⟩
          f ⁻¹ ∘ (id ∘ f ^)
            ≡⟨ ap (f ⁻¹ ∘_) (id-l (f ^)) ⟩
          f ⁻¹ ∘ f ^
            ≡⟨ linv f ⟩
          id ∎
    in mkIso (g ^ ∘ f ^) (f ⁻¹ ∘ g ⁻¹) fg-rinv fg-linv
    
  ↔to↣ : (A ↔ B) → (A ↣ B)
  ↔to↣ f =
    let inj : is-injective (f ^)
        inj x y eq = 
          x ≡⟨ refl i1 ⟩
          id x ≡˘⟨  ap (λ ○ → ○ x) (linv f) ⟩
          (f ⁻¹ ∘ f ^) x ≡⟨ refl ⟩
          (f ⁻¹) ((f ^) x) ≡⟨ ap (f ⁻¹) eq ⟩
          (f ⁻¹) ((f ^) y) ≡⟨ refl ⟩
          (f ⁻¹ ∘ f ^) y ≡⟨ ap (λ ○ → ○ y) (linv f) ⟩
          y ∎ 
    in f ^ , inj

  _↣∘↣_ : (B ↣ C) → (A ↣ B) → (A ↣ C)
  (f , inj₁) ↣∘↣ (g , inj₂) = (f ∘ g) , λ x y eq → inj₂ _ _ (inj₁ _ _ eq)



module ↔∘↔-Assoc {A B C D : Type} (C↔D : C ↔ D) (B↔C : B ↔ C) (A↔B : A ↔ B) where
  ↔∘↔-assoc : (C↔D ↔∘↔ B↔C) ↔∘↔ A↔B ≡ C↔D ↔∘↔ (B↔C ↔∘↔ A↔B)
  ↔∘↔-assoc = {!
        (C↔D ↔∘↔ B↔C) ↔∘↔ A↔B
      ≡⟨ refl ⟩
        B↔D ↔∘↔ A↔B
      ≡⟨ refl ⟩
        A↔D₁
      ≡⟨ refl ⟩
        A↔D₂
      ≡⟨ refl ⟩
        C↔D ↔∘↔ A↔C 
      ≡⟨ refl ⟩
        C↔D ↔∘↔ (B↔C ↔∘↔ A↔B) ∎!}
    where
      A↔C : A ↔ C
      A↔C = mkIso (B↔C ^ ∘ A↔B ^)
                  (A↔B ⁻¹ ∘ B↔C ⁻¹)
                  (rinv B↔C ∘ rinv A↔B)
                  (linv A↔B ∘ linv B↔C)

      B↔D : B ↔ D
      B↔D = record
        { fst = fst C↔D ∘ fst B↔C
        ; from = from B↔C ∘ from C↔D
        ; to-cong = to-cong C↔D ∘ to-cong B↔C 
        ; from-cong = from-cong B↔C ∘ from-cong C↔D
        ; inverse = fst (inverse C↔D) ∘ fst (inverse B↔C)
                  , snd (inverse B↔C) ∘ snd (inverse C↔D) }
      A↔D₁ : A ↔ D
      A↔D₁ = record
        { fst = (fst C↔D ∘ fst B↔C) ∘ fst A↔B
        ; from = from A↔B ∘ (from B↔C ∘ from C↔D)
        ; to-cong = (to-cong C↔D ∘ to-cong B↔C) ∘ to-cong A↔B
        ; from-cong = from-cong A↔B ∘ (from-cong B↔C ∘ from-cong C↔D)
        ; inverse = (fst (inverse C↔D) ∘ fst (inverse B↔C)) ∘ fst (inverse A↔B)
                  , snd (inverse A↔B) ∘ (snd (inverse B↔C) ∘ snd (inverse C↔D))
        }
      A↔D₂ : A ↔ D
      A↔D₂ = record
        { fst = fst C↔D ∘ (fst B↔C ∘ fst A↔B)
        ; from = (from A↔B ∘ from B↔C) ∘ from C↔D
        ; to-cong = to-cong C↔D ∘ (to-cong B↔C ∘ to-cong A↔B)
        ; from-cong = (from-cong A↔B ∘ from-cong B↔C) ∘ from-cong C↔D
        ; inverse = fst (inverse C↔D) ∘ (fst (inverse B↔C) ∘ fst (inverse A↔B))
                  , (snd (inverse A↔B) ∘ snd (inverse B↔C)) ∘ snd (inverse C↔D)
        }


module _  where
  open Inverse

  double-flip : ∀ {A B} (R : A ↔ B) → (flip-↔ (flip-↔ R)) ≡ R
  double-flip R = refl
  
  flip-IsId : ∀ {A B} (R : A ↔ B) → ((flip-↔ R) ↔∘↔ R) ^ ≡ id
  fst (flip-IsId {A} {B} R a) = snd (inverse R) {a} {fst R a} refl
  snd (flip-IsId {A} {B} R a) =
    begin
        a
      ≡⟨ sym (fst (inverse (flip-↔ R)) refl) ⟩
        fst (flip-↔ R) (from (flip-↔ R) a)
      ≡⟨ refl ⟩
        from R (fst R a) ∎
