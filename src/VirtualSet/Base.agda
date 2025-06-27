module VirtualSet.Base where

open import Meta.Idiom

open import 1Lab.Type
  using (Type; Typeω; ⊥; absurd; _×_; _,_; ¬_; _∘_; id)

open import 1Lab.Path using (refl; sym; ap; subst; _≡_)

-- Fin is defined as a bounded Nat in 1Lab so will require a fair amount of work to port.
open import Data.Fin.Base
  using (fin; Fin; fzero; fsuc; inject; fzero≠fsuc; fsuc≠fzero;
         Fin-absurd)

open import Data.Sum
  using (inl; inr; _⊎_)

open import Data.Nat
   using (Nat; suc-inj; zero; suc; _<_; _≤_; ≤-trans; s≤s; s≤s') renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties
   using (+-zeror; +-≤l)

open import Prim.Data.Sigma
  using (Σ; Σ-syntax; fst; snd)
open import 1Lab.HIT.Truncation
  using (∃)
open import 1Lab.Equiv using (Iso; is-iso)

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = ¬ x ≡ y

open import 1Lab.Path using (inspect)
open import Data.Nat.Base using (≤-peel)

<→≤ : ∀ {x y : Nat} → x < suc y → x ≤ y 
<→≤ {x} {y} x<sy with inspect x<sy
... | sx≤sy , eq = ≤-peel sx≤sy

open import Data.Irr using (forget)

-- I can't get this working.
-- pattern fsuc' i = fin (suc (Fin.lower i)) ⦃ forget _ ⦄
-- pattern fsuc' i = fin (suc (Fin.lower i)) ⦃ Nat.s≤s <$> (Fin.bounded i) ⦄

+→⊎ : ∀ {x y} → (Fin x ⊎ Fin y) → (Fin (x +ℕ y))
+→⊎ {x = zero} (inr i) = i
+→⊎ {x = suc x} {y} (inl i) = inject (+-≤l (suc x) y) i
+→⊎ {x = suc x} (inr i) = fsuc (+→⊎ {x = x} (inr i))

open import Data.Fin.Base using (fin-view)
  renaming (zero to vzero; suc to vsuc)

⊎→+ : ∀ {x y} → (Fin (x +ℕ y)) → (Fin x ⊎ Fin y)
⊎→+ {x = zero} i = inr i
⊎→+ {x = suc x} {y} i with fin-view i
... | vzero = inl fzero
... | vsuc i with ⊎→+ {x} {y} i
... | inl j = inl (fsuc j)
... | inr j = inr j

open import 1Lab.Equiv using (iso; Iso; is-right-inverse; is-left-inverse)

open import 1Lab.Path
+↔⊎ : ∀ {x y} → Iso (Fin x ⊎ Fin y) (Fin (x +ℕ y))
+↔⊎ = +→⊎ , 1Lab.Equiv.iso ⊎→+ eqr eql
  where
    eql : {x y : Nat} → is-left-inverse ⊎→+ +→⊎
    eql {x = zero} z = refl
    eql {x = suc x} z = refl
    eqr : {x y : Nat} → is-right-inverse ⊎→+ +→⊎
    eqr {x = zero} z = refl
    eqr {x = suc x} z = refl

import Data.Nat.Properties
  using (+-commutative; +-sucr)

⊎-swap : ∀ {X Y : Type} → (X ⊎ Y) → (Y ⊎ X)
⊎-swap {X} {Y} (inl x) = inr x
⊎-swap {X} {Y} (inr x) = inl x

⊎-swap-↔ : ∀ {X Y : Type} → Iso (X ⊎ Y) (Y ⊎ X)
⊎-swap-↔ = ⊎-swap , iso ⊎-swap swap2 swap2
  where
    swap2 : ∀ {X Y : Type} → (z : X ⊎ Y) → ⊎-swap (⊎-swap z) ≡ z
    swap2 (inl x) = refl
    swap2 (inr x) = refl

_↔_ : (X Y : Type) → Type
X ↔ Y = Iso X Y

is-injective : {X Y : Type} → (f : X → Y) → Type
is-injective {X} f = ∀ (x y : X) → f x ≡ f y → x ≡ y

_↣_ : (X Y : Type) → Type
X ↣ Y = Σ (X → Y) is-injective

-- TEMP: Polyfill
Injection : (X Y : Type) → Type
Injection X Y = X ↣ Y
Inverse : (X Y : Type) → Type
Inverse X Y = X ↔ Y
Injective : {X Y : Type} → (f : X → Y) → Type
Injective f = is-injective f

SomeFin : Type
SomeFin = Nat

⟦_⟧ : (n : SomeFin) → Type
⟦ n ⟧ = Fin n

open import Data.Irr using (Irr)

_∖_ : (A : SomeFin) → (a : Fin A) → Type
A ∖ a = Σ[ b ∈ Fin A ] Irr (a ≢ b)

open import Data.Fin.Base using (fsuc-inj)

ins : {x : Nat} → (a : ⟦ suc x ⟧) → ⟦ x ⟧ → (suc x ∖  a) 
ins {suc x} a b with fin-view a | fin-view b
... | vzero | _ = fsuc b , forget fzero≠fsuc
... | vsuc a | vzero = fzero , (forget fsuc≠fzero)
... | vsuc a | vsuc b with ins a b
... | i , forget a≢i = fsuc i , forget (λ a'≡i' → a≢i (fsuc-inj a'≡i'))

|Fin1|≡1 : (a b : ⟦ 1 ⟧) → a ≡ b
|Fin1|≡1 a b with fin-view a | fin-view b
... | vzero | vzero = refl

del : {x : Nat} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
del {zero} a (b , forget b≢a) = absurd (b≢a (|Fin1|≡1 a b))
del {suc x} a (b , forget b≢a) with fin-view a | fin-view b
... | vzero | vzero = absurd (b≢a refl)
... | vzero | vsuc b = b
... | vsuc a | vzero = fzero
... | vsuc a | vsuc b with del a (b , forget (λ a≡b → b≢a (ap fsuc a≡b)))
... | i = fsuc i

del-zero-suc : ∀ {x} (b : ⟦ x ⟧)
             → del fzero (fsuc b , forget fzero≠fsuc) ≡ b
del-zero-suc b with fin-view (del fzero (fsuc b , forget fzero≠fsuc))
... | vzero = refl
... | vsuc _ = refl

del-suc-zero : ∀ {x} (a : ⟦ suc x ⟧)
             → del (fsuc a) (fzero , forget fsuc≠fzero) ≡ fzero
del-suc-zero a with fin-view (del (fsuc a) (fzero , forget fsuc≠fzero))
... | vzero = refl

del-suc-suc : ∀ {x} (a b : ⟦ suc x ⟧) → .(a'≢b' : fsuc a ≢ fsuc b)
             → del (fsuc a) (fsuc b , forget a'≢b')
             ≡ fsuc (del a (b , forget λ a≡b → a'≢b' (ap fsuc a≡b)))
del-suc-suc a b a'≢b' with fin-view (fsuc a) | fin-view (fsuc b)
... | vsuc _ | vsuc _ = refl

del-inj : {x : Nat} → (a : ⟦ suc x ⟧)
        → (B C : (suc x ∖ a))
        → del a B ≡ del a C
        → fst B ≡ fst C
del-inj {x = zero} a (b , forget a≢b) (c , forget a≢c) b'≡c'
  with fin-view b | fin-view c
... | vzero | vzero = refl 
del-inj {x = suc x} a (b , forget a≢b) (c , forget a≢c) b'≡c'
  with fin-view a | fin-view b | fin-view c
... | vzero | vzero | _ = absurd (a≢b refl)
... | vzero | vsuc i | vzero = absurd (a≢c refl)
... | vzero | vsuc i | vsuc j =
  let i≡j : i ≡ j
      i≡j =
        i
          ≡˘⟨ del-zero-suc i ⟩
        del fzero (fsuc i , forget a≢b)
          ≡⟨ b'≡c' ⟩
        del fzero (fsuc j , forget a≢c)
          ≡⟨ del-zero-suc j ⟩
        j ∎
  in ap fsuc i≡j
... | vsuc a | vzero | vzero = refl
... | vsuc a | vzero | vsuc j = absurd (fzero≠fsuc b'≡c')
... | vsuc a | vsuc i | vzero = absurd (fsuc≠fzero b'≡c')
... | vsuc a | vsuc i | vsuc j =
  let rec :  del a (i , forget _) ≡ del a (j , forget _) → i ≡ j
      rec = del-inj a (i , (forget (λ a≡i → a≢b (ap fsuc a≡i))))
                      (j , (forget (λ a≡j → a≢c (ap fsuc a≡j))))
  in ap fsuc (rec (fsuc-inj (
        fsuc (del a (i , forget _)) ≡⟨ refl ⟩
        (del (fsuc a) ((fsuc i) , forget _)) ≡⟨ b'≡c' ⟩
        (del (fsuc a) ((fsuc j) , forget _)) ≡⟨ refl ⟩
        fsuc (del a (j , forget _ )) ∎)))

ins-inj : {x : Nat} → (a : ⟦ suc x ⟧)
        → (b c : Fin x)
        → fst (ins a b) ≡ fst (ins a c)
        → b ≡ c
ins-inj {x = zero} a b c a+b≡a+c = absurd (Fin-absurd b)
ins-inj {x = suc x} a b c a+b≡a+c with fin-view a | fin-view b | fin-view c
... | vzero | vzero | vzero = refl
... | vzero | vzero | vsuc c' = absurd (fzero≠fsuc (fsuc-inj a+b≡a+c))
... | vzero | vsuc b' | vzero = absurd (fsuc≠fzero (fsuc-inj a+b≡a+c))
... | vzero | vsuc b' | vsuc c' = fsuc-inj a+b≡a+c
... | vsuc a' | vzero | vzero = refl
... | vsuc a' | vzero | vsuc c' = absurd (fzero≠fsuc a+b≡a+c)
... | vsuc a' | vsuc b' | vzero = absurd (fsuc≠fzero a+b≡a+c)
... | vsuc a' | vsuc b' | vsuc c' =
  ap fsuc (ins-inj a' b' c' (fsuc-inj a+b≡a+c))

module Pred {x y : Nat} (f : ⟦ suc x ⟧ ↣ ⟦ suc y ⟧) where
  f-inj : is-injective (fst f)
  f-inj = snd f

  g^ : Fin x → Fin y
  g^ i =
    let (j , forget 0≢j) = ins fzero i 
    in del (fst f fzero) (fst f j , forget λ f0≡fj → 0≢j (f-inj fzero j f0≡fj))


  composition : (ai : (b₁ b₂ : ⟦ x ⟧) → fst (ins fzero b₁) ≡ fst (ins fzero b₂) → b₁ ≡ b₂)
       → (di : (B₁ B₂ : (suc y) ∖ fst f fzero)
             → del (fst f fzero) B₁ ≡ del (fst f fzero) B₂ → fst B₁ ≡ fst B₂)
       → Injective g^
  composition ai di b₁ b₂ f'b₁≡f'b₂ =
    let
      (c₁ , forget z≢c₁) = ins fzero b₁
      (c₂ , forget z≢c₂) = ins fzero b₂
    in
    ai b₁ b₂
       (f-inj c₁ c₂
         (di (fst f c₁ , forget λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
             (fst f c₂ , forget λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
             f'b₁≡f'b₂))

  g-inj : is-injective g^
  g-inj b₁ b₂ gb₁≡gb₂ = 
    let
      ai : (b₁ b₂ : ⟦ x ⟧) → fst (ins fzero b₁) ≡ fst (ins fzero b₂) → b₁ ≡ b₂
      ai = ins-inj fzero
      di : (B₁ B₂ : (suc y) ∖ fst f fzero)
         → del (fst f fzero) B₁ ≡ del (fst f fzero) B₂
         → fst B₁ ≡ fst B₂
      di = del-inj (fst f fzero)
      (c₁ , forget z≢c₁) = ins fzero b₁
      (c₂ , forget z≢c₂) = ins fzero b₂
    in
    ai b₁ b₂
       (f-inj c₁ c₂
         (di (fst f c₁ , forget λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
             (fst f c₂ , forget λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
             gb₁≡gb₂))

  g : ⟦ x ⟧ ↣ ⟦ y ⟧
  g = g^ , g-inj

open Pred using () renaming (g to pred)


infixl 8 _+_ _+ᶠ_ _-ᶠ_
_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y

open import Data.Nat.Base using (zero≠suc; suc≠zero)

sym-sub : {A' X Y : SomeFin} → (f : ⟦ A' + X ⟧ ↣ ⟦ A' + Y ⟧)
    → (A : SomeFin) → {A ≡ A'}
    → ⟦ X ⟧ ↣ ⟦ Y ⟧
sym-sub {zero} {X} {Y} f zero = f
sym-sub {zero} {X} {Y} f (suc A) {eq} = absurd (suc≠zero eq)
sym-sub {suc A'} {X} {Y} f (zero) {eq} = absurd (zero≠suc eq)
sym-sub {suc A'} {X} {Y} f (suc A) = sym-sub (pred f) A


+-commutative : ∀ (A B : SomeFin) → A + B ≡ B + A
+-commutative = Data.Nat.Properties.+-commutative

+-identityʳ : ∀ (x : SomeFin) → x + zero ≡ x
+-identityʳ zero = refl
+-identityʳ (suc n) =
  ap suc (+-identityʳ n)

∘-assoc : ∀ {A B C D} (h : C → D) (g : B → C) (f : A → B)
        → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc h g f = refl

id-r : ∀ {A B} (f : A → B)
     → f ∘ id ≡ f
id-r f = refl

id-l : ∀ {A B} (f : A → B)
     → id ∘ f ≡ f
id-l f = refl


module _ {A B C D : Type} where
  open is-iso

  flip-↔ : (A ↔ B) → (B ↔ A)
  flip-↔ (f , A↔B) = (from A↔B) , iso f (linv A↔B) (rinv A↔B)

  infixl 9 _↔∘↔_ _↣∘↣_

  _↔∘↔_ : (B ↔ C) → (A ↔ B) → (A ↔ C)
  (g , g-iso) ↔∘↔ (f , f-iso) =
    let f⁻¹ = from f-iso
        g⁻¹ = from g-iso
        fg-rinv : (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ≡ id
        fg-rinv =
          (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) ≡⟨ sym (∘-assoc g f (f⁻¹ ∘ g⁻¹)) ⟩
          g ∘ (f ∘ (f⁻¹ ∘ g⁻¹)) ≡⟨ ap (g ∘_) (∘-assoc f f⁻¹ g⁻¹) ⟩
          g ∘ ((f ∘ f⁻¹) ∘ g⁻¹) ≡⟨ ap (λ ○ → g ∘ (○ ∘ g⁻¹)) (funext (rinv f-iso)) ⟩
          g ∘ (id ∘ g⁻¹) ≡⟨ ap (g ∘_) (id-l g⁻¹) ⟩
          g ∘ g⁻¹ ≡⟨ funext (rinv g-iso) ⟩
          id ∎

        fg-linv : (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ≡ id
        fg-linv =
          (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) ≡⟨ sym (∘-assoc f⁻¹ g⁻¹ (g ∘ f)) ⟩
          f⁻¹ ∘ (g⁻¹ ∘ (g ∘ f)) ≡⟨ ap (f⁻¹ ∘_) (∘-assoc g⁻¹ g f) ⟩
          f⁻¹ ∘ ((g⁻¹ ∘ g) ∘ f) ≡⟨ ap (λ ○ → f⁻¹ ∘ (○ ∘ f)) (funext (linv g-iso)) ⟩
          f⁻¹ ∘ (id ∘ f) ≡⟨ ap (f⁻¹ ∘_) (id-l f) ⟩
          f⁻¹ ∘ f ≡⟨ funext (linv f-iso) ⟩
          id ∎

    in (g ∘ f) , iso (f⁻¹ ∘ g⁻¹)
          (λ c → 
            (g ∘ f) ((f⁻¹ ∘ g⁻¹) c) ≡⟨ refl ⟩
            ((g ∘ f) ∘ (f⁻¹ ∘ g⁻¹)) c ≡⟨ ap (λ ○ → ○ c) fg-rinv ⟩
            id c ≡⟨ refl ⟩
            c ∎)
          (λ a → 
            (f⁻¹ ∘ g⁻¹) ((g ∘ f) a) ≡⟨ refl ⟩
            ((f⁻¹ ∘ g⁻¹) ∘ (g ∘ f)) a ≡⟨ ap (λ ○ → ○ a) fg-linv ⟩
            id a ≡⟨ refl ⟩
            a ∎)

  ↔to↣ : (A ↔ B) → (A ↣ B)
  ↔to↣ (f , f-iso) =
    let f⁻¹ = from f-iso
    in
    f , λ x y eq →
      x ≡⟨ sym (linv f-iso x) ⟩
      f⁻¹ (f x) ≡⟨ ap f⁻¹ eq ⟩
      f⁻¹ (f y) ≡⟨ linv f-iso y ⟩
      y ∎

  {-


  _↣∘↣_ : (B ↣ C) → (A ↣ B) → (A ↣ C)
  (f , inj₁) ↣∘↣ (g , inj₂) = (f ∘ g) , λ x y eq → inj₂ _ _ (inj₁ _ _ eq)

  ↔-IsId : ∀ {A} → (R : A ↔ A) → Typeω
  ↔-IsId {A} (f , iso f⁻¹ _ _) = ∀ a → f a ≡ a × a ≡ f⁻¹ a
  -- -}

{-
module _ {A B C D : Type} where
  open Inverse
  open Injection
  
  flip-↔ : (A ↔ B) → (B ↔ A)
  flip-↔ A↔B = record
    { fst = from A↔B
    ; from = fst A↔B
    ; to-cong = from-cong A↔B
    ; from-cong = to-cong A↔B
    ; inverse = (snd (inverse A↔B)) , (fst (inverse A↔B))
    }

  infixl 9 _↔∘↔_ _↣∘↣_

  _↔∘↔_ : (B ↔ C) → (A ↔ B) → (A ↔ C)
  B↔C ↔∘↔ A↔B  = record
    { fst = fst B↔C ∘ fst A↔B 
    ; from = from A↔B ∘ from B↔C
    ; fst-cong = fst-cong B↔C ∘ to-cong A↔B 
    ; from-cong = from-cong A↔B ∘ from-cong B↔C 
    ; inverse = fst (inverse B↔C) ∘ fst (inverse A↔B)
              , snd (inverse A↔B) ∘ snd (inverse B↔C)
    }

  ↔to↣ : (A ↔ B) → (A ↣ B)
  ↔to↣ R = record
    { fst = Inverse.fst R 
    ; cong = to-cong R 
    ; injective = λ {x} {y} Rx≡Ry → 
      begin
          x
        ≡⟨ sym ((snd (inverse R) {x} {fst R y}) (sym Rx≡Ry)) ⟩
          R .from (fst R y)
        ≡⟨ (snd (inverse R)) refl ⟩
          y ∎
    }

  _↣∘↣_ : (B ↣ C) → (A ↣ B) → (A ↣ C)
  B↔C ↣∘↣ A↔B  = record
    { fst = fst B↔C ∘ fst A↔B 
    ; cong = cong B↔C ∘ cong A↔B 
    ; injective = injective A↔B ∘ injective B↔C
    }

  ↔-IsId : ∀ {A} → (R : A ↔ A) → Typeω
  ↔-IsId {A} R = ∀ (a : A) → fst R a ≡ a × a ≡ from R a

{-
             
module _ {A B C D : Typeω} where
  open Inverse

  ∘-assoc : (C→D : C → D) → (B→C : B → C) → (A→B : A → B)
          → (C→D ∘ B→C) ∘ A→B ≡ C→D ∘ (B→C ∘ A→B)
  ∘-assoc C→D B→C A→B = ap (λ _ x → C→D (B→C (A→B x))) refl

  ↔∘↔-assoc : (C↔D : C ↔ D) → (B↔C : B ↔ C) → (A↔B : A ↔ B)
            → (C↔D ↔∘↔ B↔C) ↔∘↔ A↔B ≡ C↔D ↔∘↔ (B↔C ↔∘↔ A↔B)
  ↔∘↔-assoc C↔D B↔C A↔B =
    begin
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
        C↔D ↔∘↔ (B↔C ↔∘↔ A↔B) ∎
    where
      A↔C : A ↔ C
      A↔C = record
        { fst = fst B↔C ∘ fst A↔B
        ; from = from A↔B ∘ from B↔C
        ; to-cong = to-cong B↔C ∘ to-cong A↔B 
        ; from-cong = from-cong A↔B ∘ from-cong B↔C
        ; inverse = fst (inverse B↔C) ∘ fst (inverse A↔B)
                  , snd (inverse A↔B) ∘ snd (inverse B↔C)
        }
      B↔D : B ↔ D
      B↔D = record
        { fst = fst C↔D ∘ fst B↔C
        ; from = from B↔C ∘ from C↔D
        ; to-cong = to-cong C↔D ∘ to-cong B↔C 
        ; from-cong = from-cong B↔C ∘ from-cong C↔D
        ; inverse = fst (inverse C↔D) ∘ fst (inverse B↔C)
                  , snd (inverse B↔C) ∘ snd (inverse C↔D)
        }
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
  
  flip-IsId : ∀ {A B} (R : A ↔ B) → ↔-IsId ((flip-↔ R) ↔∘↔ R)
  fst (flip-IsId {A} {B} R a) = snd (inverse R) {a} {fst R a} refl
  snd (flip-IsId {A} {B} R a) =
    begin
        a
      ≡⟨ sym (fst (inverse (flip-↔ R)) refl) ⟩
        fst (flip-↔ R) (from (flip-↔ R) a)
      ≡⟨ refl ⟩
        from R (fst R a) ∎

module _ where
  open Inverse

  swap : ∀ {A B} → ⟦ A + B ⟧ ↔ ⟦ B + A ⟧
  swap = (flip-↔ +↔⊎) ↔∘↔ ⊎-swap-↔ ↔∘↔ +↔⊎

  swap-involutive : ∀ {A B : SomeFin} {x} → ↔-IsId (swap ↔∘↔ swap)
  swap-involutive {A} {B} {x} = flip-IsId swap

  inl-injective : ∀ {A} {x y : A} → inl x ≡ inl y → x ≡ y
  inl-injective refl = refl
  inr-injective : ∀ {A} {x y : A} → inr x ≡ inr y → x ≡ y
  inr-injective refl = refl

  map↣⊎ : ∀ {A B C D} → (A ↣ B) → (C ↣ D) → ((A ⊎ C) ↣ (B ⊎ D))
  map↣⊎ {A} {B} {C} {D} f g = record
    { fst = h
    ; cong = ap h
    ; injective = inj
    }
    where open Injection
          h : (A ⊎ C) → (B ⊎ D)
          h (inl a) = inl (fst f a)
          h (inr c) = inr (fst g c)
          inj : ∀ {x y} → h x ≡ h y → x ≡ y
          inj {inl x} {inl y} =
            ap inl ∘ injective f ∘ inl-injective
          inj {inr x} {inr y} =
            ap inr ∘ injective g ∘ inr-injective

  id↣ : ∀ {A} → A ↣ A
  id↣ {A} = record
    { fst = id
    ; cong = id
    ; injective = id
    }

  ⊎⊥ˡ : ∀ {A} → (A ⊎ ⟦ zero ⟧) ↔ A
  ⊎⊥ˡ {A} = record
    { fst = f
    ; from = inl
    ; to-cong = f-cong
    ; from-cong = ap inl
    ; inverse = invˡ , invʳ
    }
    where
      f : (A ⊎ ⟦ zero ⟧) → A
      f (inl x) = x 
      f-cong : {x' y' : A ⊎ ⟦ zero ⟧} → x' ≡ y' → f x' ≡ f y' 
      f-cong {inl x} {inl y} = inl-injective
      invˡ : ∀ {x} {y} → y ≡ inl x → f y ≡ x
      invˡ {x} {inl y} = inl-injective
      invʳ : ∀ {x} {y} → y ≡ f x → inl y ≡ x
      invʳ {inl x} {y} = ap inl
      
  ⊎⊥ʳ : ∀ {A} → (⟦ zero ⟧ ⊎ A) ↔ A
  ⊎⊥ʳ {A} = record
    { to = f
    ; from = inr
    ; to-cong = f-cong
    ; from-cong = ap inr
    ; inverse = invˡ , invʳ
    }
    where
      f : (⟦ zero ⟧ ⊎ A) → A
      f (inr x) = x 
      f-cong : {x' y' : ⟦ zero ⟧ ⊎ A} → x' ≡ y' → f x' ≡ f y' 
      f-cong {inr x} {inr y} = inr-injective
      invˡ : ∀ {x} {y} → y ≡ inr x → f y ≡ x
      invˡ {x} {inr y} = inr-injective
      invʳ : ∀ {x} {y} → y ≡ f x → inr y ≡ x
      invʳ {inr x} {y} = ap inr


module _ where
  open Injection 

  splice : {X : SomeFin} → (a : ⟦ suc X ⟧) → ⟦ X ⟧ ↔ (suc X ∖ a)
  splice {X} a = record
    { fst = ins a
    ; from = del a 
    ; to-cong = ap (ins a)
    ; from-cong = ap (del a)
    ; inverse = {!!} , {!!}
    }

  splice-inverseˡ : {X : SomeFin} → (a : ⟦ suc X ⟧) → Inverseˡ (del a) (ins a)
  splice-inverseˡ {zero} a {()} {y} y≡x+
  splice-inverseˡ {suc X} fzero {fzero} {fsuc y , y'≢0} y≡x+ = {!!}
  splice-inverseˡ {suc X} (fsuc a) {fzero} {fzero , 0≢a'} y≡x+ = refl
  splice-inverseˡ {suc X} fzero {fsuc x} {fsuc (fsuc y) , y≢0} =
    λ L → 
      {!!} ( ap inl L)
         
     -- ap fsuc {!suc-inj (suc-inj (inl-injective!} --  (ap inl {!y≡x+!})
  splice-inverseˡ {suc X} (fsuc a) {fsuc x} {fsuc y , y'≢a'} y≡x+ = {!!}
    -- begin
    --     del a y
    --   ≡⟨ {!!} ⟩
    --     x ∎

-- dec : ∀ {X Y : SomeFin} → ((⟦ X ⟧ ⊎ ⟦ 1 ⟧) ↣ (⟦ Y ⟧ ⊎ ⟦ 1 ⟧))
--     → (⟦ X ⟧ ↣ ⟦ Y ⟧)
-- dec {X} {Y} f = {!!}
--     where
--       g : ⟦ X ⟧ → ⟦ Y ⟧
--       g x = {!!}

{-
  _-ᶠ_ : {A' X Y : SomeFin} → (f : (⟦ X ⟧ ⊎ ⟦ A' ⟧) ↣ (⟦ Y ⟧ ⊎ ⟦ A' ⟧))
      → (A : SomeFin) → {A ≡ A'}
      → ⟦ X ⟧ ↣ ⟦ Y ⟧
  _-ᶠ_ {A' = zero} f zero = ↔to↣ ⊎⊥ˡ ↣∘↣ f ↣∘↣ ↔to↣ (flip-↔ ⊎⊥ˡ)
  _-ᶠ_ {A' = suc A'} {X} {Y} f (suc A) {eq} = _-ᶠ_ {A'} g A 
    where
      g : (⟦ X ⟧ ⊎ ⟦ A' ⟧) ↣ (⟦ Y ⟧ ⊎ ⟦ A' ⟧)
      g = map↣⊎ id↣ {!ins!}  ↣∘↣ f ↣∘↣ map↣⊎ id↣ {!!}

  -- _-ᶠ_ {A'} {X} {Y} f A =
  --   let g = (↔to↣ (swap {Y} {A'})) ↣∘↣ f ↣∘↣ (↔to↣ (swap {A'} {X}))
  --   in sym-sub g A


  _+ᶠ-sym_ : ∀ {X Y : SomeFin} (g : ⟦ X ⟧ ↣ ⟦ Y ⟧) → (A : SomeFin)
          → ⟦ X + A ⟧ ↣ ⟦ Y + A ⟧
  _+ᶠ-sym_ {X} {Y} g A = ↔to↣ (flip-↔ +↔⊎) ↣∘↣ map↣⊎ g (id↣ {⟦ A ⟧}) ↣∘↣ ↔to↣ +↔⊎

  _+ᶠ-sym_ : ∀ {X Y : SomeFin} (g : ⟦ X ⟧ ↣ ⟦ Y ⟧) → (A : SomeFin)
          → ⟦ A + X ⟧ ↣ ⟦ A + Y ⟧
  _+ᶠ-sym_ {X} {Y} g zero = g
  _+ᶠ-sym_ {X} {Y} g (suc A) = ↔to↣ (flip-↔ +↔⊎) ↣∘↣ map↣⊎ (id↣ {⟦ 1 ⟧}) (g +ᶠ-sym A) ↣∘↣ ↔to↣ +↔⊎
-}
    record
      { fst = g''
      ; cong = ap g''
      ; injective = inj
      }
     where
       g' = g +ᶠ-sym A
       g'' : Fin (suc A + X) → Fin (suc A + Y)
       g'' fzero = fzero
       g'' (fsuc a) = fsuc (fst g' a)
       inj : Injective g''
       inj {fzero} {fzero} eq = refl
       inj {fsuc x} {fsuc y} eq =
         begin
              fsuc x
            ≡⟨ ap fsuc (injective g' (suc-inj eq)) ⟩
              fsuc y ∎

_+ᶠ_ : ∀ {X Y : SomeFin} (g : Fin X ↣ Fin Y) → (A : SomeFin) → Fin (X + A) ↣ Fin (Y + A)
_+ᶠ_ {X} {Y} g A =
  subst (λ h → Fin (X + A) ↣ Fin h)
          (sym (+-commutative Y A))
    (subst (λ h → Fin h ↣ Fin (A + Y))
             (sym (+-commutative X A))
       (g +ᶠ-sym A))

_⊙_ : ∀ {X Y fzero} → (Fin Y ↣ Fin fzero) → (Fin X ↣ Fin Y) → (Fin X ↣ Fin fzero)
_⊙_ g f = record
  { fst = fst g ∘ fst f 
  ; cong = cong g ∘ cong f
  ; injective = injective f ∘ injective g
  }

module theorem1-2 where
  private
    variable A B X Y fzero : SomeFin

  lemma1-3 : ∀ (f : Fin X ↣ Fin Y) → (f +ᶠ A) -ᶠ A ≡ f
  lemma1-3 {A = zero} f = 
    begin
        f +ᶠ zero -ᶠ zero
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ {!!} ⟩
        f ∎

  lemma1-3 {A = suc A} f = {!!}

  --lemma1-3 : ∀ {X Y : SomeFin} → (f : Fin (X + 0) ↣ Fin (Y + 0)) → (f -ᶠ 0) ≡ f

  --lemma1 : ∀ {A X Y fzero} → (f : Fin (Y + A) ↣ Fin (fzero + A)) → (g : Fin X ↣ Fin Y) → (f ⊙ (g +ᶠ A)) -ᶠ A ≡ (f -ᶠ A) ⊙ g 
  --lemma1 {zero} {X} {Y} {fzero} f g = 
  --  begin
  --      ((f ⊙ (g +ᶠ 0)) -ᶠ 0)
  --    ≡⟨ {!!} ⟩
  --      {!!}
  --    ≡⟨ {!!} ⟩
  --      ((f -ᶠ 0) ⊙ g ) ∎

  --lemma1 {suc A} {X} {Y} {fzero} f g = {!!}
  --  -- begin
  --  --     ((f ⊙ (g +ᶠ A)) -ᶠ A)
  --  --   ≡⟨ {!!} ⟩
  --  --     ((f -ᶠ A) ⊙ g ) ∎
-- -}
-- -}
-- -}
-- -}
