module VSet.VSet where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Fin.Default
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties


SomeFin : Type
SomeFin = ℕ

⟦_⟧ : (n : SomeFin) → Type
⟦ n ⟧ = Fin n

_∖_ : (A : SomeFin) → (a : Fin A) → Type
A ∖ a = Σ[ b ∈ Fin A ] a ≢ b

ins : {x : ℕ} → (a : ⟦ suc x ⟧) → ⟦ x ⟧ → (suc x ∖  a) 
-- ins {suc x} a b with fin-view a | fin-view b
-- ... | vzero | _ = fsuc b , fzero≠fsuc
-- ... | vsuc a | vzero = fzero , (fsuc≠fzero)
-- ... | vsuc a | vsuc b with ins a b
-- ... | i , a≢i = fsuc i , (λ a'≡i' → a≢i (fsuc-inj a'≡i'))

|Fin1|≡1 : (a b : ⟦ 1 ⟧) → a ≡ b
-- |Fin1|≡1 a b with fin-view a | fin-view b
-- ... | vzero | vzero = refl

del : {x : ℕ} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
-- del {zero} a (b , b≢a) = absurd (b≢a (|Fin1|≡1 a b))
-- del {suc x} a (b , b≢a) with fin-view a | fin-view b
-- ... | vzero | vzero = absurd (b≢a refl)
-- ... | vzero | vsuc b = b
-- ... | vsuc a | vzero = fzero
-- ... | vsuc a | vsuc b with del a (b , (λ a≡b → b≢a (ap fsuc a≡b)))
-- ... | i = fsuc i

del-zero-suc : ∀ {x} (b : ⟦ x ⟧)
             → del fzero (fsuc b , fzero≢fsuc b) ≡ b
-- del-zero-suc b with fin-view (del fzero (fsuc b , fzero≠fsuc))
-- ... | vzero = refl
-- ... | vsuc _ = refl

del-suc-zero : ∀ {x} (a : ⟦ suc x ⟧)
             → del (fsuc a) (fzero , fsuc≢fzero a) ≡ fzero
-- del-suc-zero a with fin-view (del (fsuc a) (fzero , fsuc≠fzero))
-- ... | vzero = refl
del-suc-suc : ∀ {x} (a b : ⟦ suc x ⟧) → .(a'≢b' : fsuc a ≢ fsuc b)
             → del (fsuc a) (fsuc b , {!!})
             ≡ fsuc (del a (b , {!λ a≡b → a'≢b' (ap fsuc a≡b)!}))
-- del-suc-suc a b a'≢b' with fin-view (fsuc a) | fin-view (fsuc b)
-- ... | vsuc _ | vsuc _ = refl

del-inj : {x : ℕ} → (a : ⟦ suc x ⟧)
        → (B C : (suc x ∖ a))
        → del a B ≡ del a C
        → fst B ≡ fst C
-- del-inj {x = zero} a (b , a≢b) (c , a≢c) b'≡c'
--   with fin-view b | fin-view c
-- ... | vzero | vzero = refl 
-- del-inj {x = suc x} a (b , a≢b) (c , a≢c) b'≡c'
--   with fin-view a | fin-view b | fin-view c
-- ... | vzero | vzero | _ = absurd (a≢b refl)
-- ... | vzero | vsuc i | vzero = absurd (a≢c refl)
-- ... | vzero | vsuc i | vsuc j =
--   let i≡j : i ≡ j
--       i≡j =
--         i
--           ≡˘⟨ del-zero-suc i ⟩
--         del fzero (fsuc i , a≢b)
--           ≡⟨ b'≡c' ⟩
--         del fzero (fsuc j , a≢c)
--           ≡⟨ del-zero-suc j ⟩
--         j ∎
--   in ap fsuc i≡j
-- ... | vsuc a | vzero | vzero = refl
-- ... | vsuc a | vzero | vsuc j = absurd (fzero≠fsuc b'≡c')
-- ... | vsuc a | vsuc i | vzero = absurd (fsuc≠fzero b'≡c')
-- ... | vsuc a | vsuc i | vsuc j =
--   let rec :  del a (i , _) ≡ del a (j , _) → i ≡ j
--       rec = del-inj a (i , ((λ a≡i → a≢b (ap fsuc a≡i))))
--                       (j , ((λ a≡j → a≢c (ap fsuc a≡j))))
--   in ap fsuc (rec (fsuc-inj (
--         fsuc (del a (i , _)) ≡⟨ refl ⟩
--         (del (fsuc a) ((fsuc i) , _)) ≡⟨ b'≡c' ⟩
--         (del (fsuc a) ((fsuc j) , _)) ≡⟨ refl ⟩
--         fsuc (del a (j , _ )) ∎)))


ins-inj : {x : ℕ} → (a : ⟦ suc x ⟧)
        → (b c : Fin x)
        → fst (ins a b) ≡ fst (ins a c)
        → b ≡ c
-- ins-inj {x = zero} a b c a+b≡a+c = absurd (Fin-absurd b)
-- ins-inj {x = suc x} a b c a+b≡a+c with fin-view a | fin-view b | fin-view c
-- ... | vzero | vzero | vzero = refl
-- ... | vzero | vzero | vsuc c' = absurd (fzero≠fsuc (fsuc-inj a+b≡a+c))
-- ... | vzero | vsuc b' | vzero = absurd (fsuc≠fzero (fsuc-inj a+b≡a+c))
-- ... | vzero | vsuc b' | vsuc c' = fsuc-inj a+b≡a+c
-- ... | vsuc a' | vzero | vzero = refl
-- ... | vsuc a' | vzero | vsuc c' = absurd (fzero≠fsuc a+b≡a+c)
-- ... | vsuc a' | vsuc b' | vzero = absurd (fsuc≠fzero a+b≡a+c)
-- ... | vsuc a' | vsuc b' | vsuc c' =
--   ap fsuc (ins-inj a' b' c' (fsuc-inj a+b≡a+c))

module Pred {x y : ℕ} (f : ⟦ suc x ⟧ ↣ ⟦ suc y ⟧) where
  f-inj : is-injective (fst f)
  f-inj = snd f

  g^ : Fin x → Fin y
  g^ i =
    let (j , 0≢j) = ins fzero i 
    in del (fst f fzero) (fst f j , λ f0≡fj → 0≢j (f-inj fzero j f0≡fj))


  composition : (ai : (b₁ b₂ : ⟦ x ⟧) → fst (ins fzero b₁) ≡ fst (ins fzero b₂) → b₁ ≡ b₂)
       → (di : (B₁ B₂ : (suc y) ∖ fst f fzero)
             → del (fst f fzero) B₁ ≡ del (fst f fzero) B₂ → fst B₁ ≡ fst B₂)
       → Injective g^
  composition ai di b₁ b₂ f'b₁≡f'b₂ =
    let
      (c₁ , z≢c₁) = ins fzero b₁
      (c₂ , z≢c₂) = ins fzero b₂
    in
    ai b₁ b₂
       (f-inj c₁ c₂
         (di (fst f c₁ , λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
             (fst f c₂ , λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
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
      (c₁ , z≢c₁) = ins fzero b₁
      (c₂ , z≢c₂) = ins fzero b₂
    in
    ai b₁ b₂
       (f-inj c₁ c₂
         (di (fst f c₁ , λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
             (fst f c₂ , λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
             gb₁≡gb₂))

  g : ⟦ x ⟧ ↣ ⟦ y ⟧
  g = g^ , g-inj

open Pred using () renaming (g to pred)

{-



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

{-

module _ where
  open Inverse

  swap : ∀ {A B} → ⟦ A + B ⟧ ↔ ⟦ B + A ⟧
  swap = (flip-↔ +↔⊎) ↔∘↔ ⊎-swap-↔ ↔∘↔ +↔⊎

  swap-involutive : ∀ {A B : SomeFin} {x} → (swap ↔∘↔ swap) ^ ≡ id
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
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
