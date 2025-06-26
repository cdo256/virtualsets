module VirtualSet.Base where

open import Meta.Idiom

open import 1Lab.Type
  using (Type; ⊥; absurd; _×_; _,_; ¬_)
-- Fin is defined as a bounded Nat in 1Lab so will require a fair amount of work to port.
open import Data.Fin.Base
  using (fin; Fin; fzero; fsuc; inject)

open import Data.Sum
  using (inl; inr; _⊎_) renaming (swap to ⊎-swap)

open import Data.Nat
   using (Nat; suc-inj; zero; suc; _<_; _≤_; ≤-trans; s≤s; s≤s') renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties
   using (+-zeror; +-≤l)

open import Prim.Data.Sigma
  using (Σ; Σ-syntax; fst; snd)
open import 1Lab.HIT.Truncation
  using (∃)
open import 1Lab.Equiv using (Iso; is-iso)

open import 1Lab.Path using (refl ; sym ; trans ; cong ; subst ; _≡_)

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
  using (+-comm; +-suc)
open import Data.Sum.Properties
  using () renaming (swap-↔ to ⊎-swap-↔)
open import Level
  using (Setω; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality
  using (inspect; [_])
open import Function.Base
  using (_∘_; id)
open import Function.Bundles
  using (_↣_; _↔_; Injection; Inverse)
open import Algebra.Definitions
  using (RightIdentity)
open import Function.Definitions
  using (Injective; Congruent;
         Inverseˡ; Inverseʳ; Inverseᵇ)

{-
 
-- open import Cubical.HITs.SetQuotients.Base

open ≡-Reasoning
private
  variable
    c ℓ : Level.Level




SomeFin : Setω
SomeFin = Nat

⟦_⟧ : (n : SomeFin) → Setω
⟦ n ⟧ = Fin n

-- _∖_ : (A : SomeFin) → (a : Fin A) → Setω
-- A ∖ a = Σ[ b ∈ Fin A ] .(a ≢ b)

record _∖_ (A : SomeFin) (a : Fin A) : Setω where
  constructor _,_
  field
    val : Fin A
    .≠ : a ≢ val
open _∖_

add : {x : Nat} → (a : ⟦ suc x ⟧) → ⟦ x ⟧ → (suc x ∖  a) 
add {suc x} fzero b = fsuc b , λ ()
add {suc x} (fsuc a) fzero = fzero , λ ()
add {suc x} (fsuc a) (fsuc b) =
  let
    (c , a≢c) = add a b
  in fsuc (val (add a b)) , λ a'≡c' → a≢c (suc-inj a'≡c')

del : {x : Nat} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
del {ℕ.zero} fzero (fzero , 0≢0) = absurt (0≢0 ≡.refl)
del {suc x} fzero (fzero , 0≢0) = absurd (0≢0 ≡.refl)
del {suc x} fzero (fsuc b , a≢b) = b
del {suc x} (fsuc a) (fzero , a≢b) = fzero
del {suc x} (fsuc a) (fsuc b , a'≢b') =
  fsuc (del {x} a (b , λ a≡b → absurd (a'≢b' (≡.cong fsuc a≡b))))

del-zero-suc : ∀ {x} (b : ⟦ x ⟧) (a≢b : fzero ≢ fsuc b) → del fzero (fsuc b , a≢b) ≡ b
del-zero-suc b a≢b with del fzero (fsuc b , a≢b) | inspect (del fzero) (fsuc b , a≢b)
... | fzero | [ eq ] = ≡.sym eq
... | fsuc X | [ eq ] = ≡.sym eq

del-inj : {x : Nat} → (a : ⟦ suc x ⟧)
        → (B₁ B₂ : (suc x ∖ a))
        → del a B₁ ≡ del a B₂
        → val B₁ ≡ val B₂
del-inj fzero (fzero , a≢b₁) (fzero , a≢b₂) b₁'≡b₂' =
  absurd (a≢b₁ ≡.refl)
del-inj fzero (fzero , a≢b₁) (fsuc b₂ , a≢b₂) b₁'≡b₂' =
  absurd (a≢b₁ ≡.refl)
del-inj fzero (fsuc b₁ , a≢b₁) (fzero , a≢b₂) b₁'≡b₂' =
  absurd (a≢b₂ ≡.refl)
del-inj fzero (fsuc b₁ , a≢b₁) (fsuc b₂ , a≢b₂) b₁'≡b₂' =
  let b₁' = del fzero (fsuc b₁ , a≢b₁)
      b₂' = del fzero (fsuc b₂ , a≢b₂)
      b₁'≡b₁ : b₁' ≡ b₁
      b₁'≡b₁ = del-zero-suc b₁ a≢b₁
      b₂'≡b₂ : b₂' ≡ b₂
      b₂'≡b₂ = del-zero-suc b₂ a≢b₂
  in begin
      fsuc b₁
    ≡⟨ ≡.cong fsuc (≡.sym b₁'≡b₁) ⟩
      fsuc b₁'
    ≡⟨ ≡.cong fsuc b₁'≡b₂' ⟩
      fsuc b₂'
    ≡⟨ ≡.cong fsuc b₂'≡b₂ ⟩
      fsuc b₂ ∎
del-inj (fsuc a) (fzero , a≢b₁) (fzero , a≢b₂) b₁'≡b₂' = ≡.refl
del-inj (fsuc a) (fzero , a≢b₁) (fsuc b₂ , a≢b₂) b₁'≡b₂'
  with del (fsuc a) (fzero , a≢b₁) | inspect (del (fsuc a)) (fzero , a≢b₁) | del (fsuc a) (fsuc b₂  , a≢b₂) | inspect (del (fsuc a)) (fsuc b₂ , a≢b₂)
... | fzero | [ eq₁ ] | fzero | ()
... | fzero | _ | fsuc _ | _ = absurd (0≢1+n b₁'≡b₂')
... | fsuc X | () | _ | _
del-inj (fsuc a) (fsuc b₁ , a≢b₁) (fzero , a≢b₂) b₁'≡b₂' =
  ≡.sym (del-inj (fsuc a) (fzero , a≢b₂) (fsuc b₁ , a≢b₁) (≡.sym b₁'≡b₂'))
del-inj (fsuc a) (fsuc b₁ , sa≢sb₁) (fsuc b₂ , sa≢sb₂) b₁'≡b₂'
  with del (fsuc a) (fsuc b₁ , sa≢sb₁) | inspect (del (fsuc a)) (fsuc b₁ , sa≢sb₁) | del (fsuc a) (fsuc b₂  , sa≢sb₂) | inspect (del (fsuc a)) (fsuc b₂ , sa≢sb₂) | b₁'≡b₂'
... | fsuc c₁ | [ eq₁ ] | fsuc c₂ | [ eq₂ ] | _ =
  ≡.cong fsuc (del-inj a (b₁ , λ a≡b₁ → sa≢sb₁ (≡.cong fsuc a≡b₁))
                      (b₂ , λ a≡b₂ → sa≢sb₂ (≡.cong fsuc a≡b₂))
                      (suc-inj b₁'≡b₂'))

add-inj : {x : Nat} → (a : ⟦ suc x ⟧)
        → (b₁ b₂ : Fin x)
        → val (add a b₁) ≡ val (add a b₂)
        → b₁ ≡ b₂
add-inj fzero fzero fzero c₁≡c₂ = ≡.refl
add-inj fzero (fsuc b₁) (fsuc b₂) c₁≡c₂
  with add fzero b₁ | inspect (add fzero) b₁ | add fzero b₂ | inspect (add fzero) b₂
... | c₁ , z≢c₁ | [ eq₁ ] | c₂ , z≢c₂ | [ eq₂ ] = suc-inj c₁≡c₂
add-inj (fsuc a) fzero fzero c₁≡c₂ = ≡.refl
add-inj (fsuc a) (fsuc b₁) (fsuc b₂) c₁≡c₂
  with add (fsuc a) (fsuc b₁) | inspect (add (fsuc a)) (fsuc b₁) | add (fsuc a) (fsuc b₂) | inspect (add (fsuc a)) (fsuc b₂)
... | fsuc c₁ , sa≢sc₁ | [ eq₁ ] | fsuc c₂ , sa≢sc₂ | [ eq₂ ] =
  ≡.cong fsuc (add-inj a b₁ b₂ (suc-inj c₁≡c₂))

module _ {x y : Nat} (f : ⟦ suc x ⟧ ↣ ⟦ suc y ⟧) where
  open Injection

  f' : Fin x → Fin y
  f' i =
    let (j , 0≢j) = add fzero i 
    in del (to f fzero) (to f j , λ f0≡fj → 0≢j (injective f f0≡fj))

  comp : (ai : (b₁ b₂ : ⟦ x ⟧) → val (add fzero b₁) ≡ val (add fzero b₂) → b₁ ≡ b₂)
       → (di : (B₁ B₂ : (suc y) ∖ to f fzero)
             → del (to f fzero) B₁ ≡ del (to f fzero) B₂ → val B₁ ≡ val B₂)
       → Injective _≡_ _≡_ f'
  comp ai di {b₁} {b₂} f'b₁≡f'b₂ =
    let
      (c₁ , z≢c₁) = add fzero b₁
      (c₂ , z≢c₂) = add fzero b₂
    in
    ai b₁ b₂
       (injective f {c₁} {c₂}
            (di (to f c₁ , λ fz≡fc₁ → z≢c₁ (injective f {fzero} {c₁} fz≡fc₁))
                (to f c₂ , λ fz≡fc₂ → z≢c₂ (injective f {fzero} {c₂} fz≡fc₂))
                f'b₁≡f'b₂))

  sub : ⟦ x ⟧ ↣ ⟦ y ⟧
  sub = record
    { to = f'
    ; cong = ≡.cong f'
    ; injective = comp (add-inj fzero) (del-inj (to f fzero))
    }

infixl 6 _+_ _+ᶠ_ _-ᶠ_
_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y

sym-sub : {A' X Y : SomeFin} → (f : ⟦ A' + X ⟧ ↣ ⟦ A' + Y ⟧)
    → (A : SomeFin) → {A ≡ A'}
    → ⟦ X ⟧ ↣ ⟦ Y ⟧
sym-sub {ℕ.zero} {X} {Y} f ℕ.zero = f
sym-sub {suc A'} {X} {Y} f (suc A) = (sym-sub (sub f) A)

+-comm : ∀ (A B : SomeFin) → A + B ≡ B + A
+-comm = Data.Nat.Properties.+-comm

+-identityʳ : ∀ (x : SomeFin) → x + ℕ.zero ≡ x
+-identityʳ ℕ.zero = ≡.refl
+-identityʳ (suc n) =
  ≡.cong suc (+-identityʳ n)


module _ {A B C D : Setω} where
  open Inverse
  open Injection
  
  flip-↔ : (A ↔ B) → (B ↔ A)
  flip-↔ A↔B = record
    { to = from A↔B
    ; from = to A↔B
    ; to-cong = from-cong A↔B
    ; from-cong = to-cong A↔B
    ; inverse = (snd (inverse A↔B)) , (fst (inverse A↔B))
    }

  infixl 9 _↔∘↔_ _↣∘↣_

  _↔∘↔_ : (B ↔ C) → (A ↔ B) → (A ↔ C)
  B↔C ↔∘↔ A↔B  = record
    { to = to B↔C ∘ to A↔B 
    ; from = from A↔B ∘ from B↔C
    ; to-cong = to-cong B↔C ∘ to-cong A↔B 
    ; from-cong = from-cong A↔B ∘ from-cong B↔C 
    ; inverse = fst (inverse B↔C) ∘ fst (inverse A↔B)
              , snd (inverse A↔B) ∘ snd (inverse B↔C)
    }

  ↔to↣ : (A ↔ B) → (A ↣ B)
  ↔to↣ R = record
    { to = Inverse.to R 
    ; cong = to-cong R 
    ; injective = λ {x} {y} Rx≡Ry → 
      begin
          x
        ≡⟨ ≡.sym ((snd (inverse R) {x} {to R y}) (≡.sym Rx≡Ry)) ⟩
          R .from (to R y)
        ≡⟨ (snd (inverse R)) ≡.refl ⟩
          y ∎
    }

  _↣∘↣_ : (B ↣ C) → (A ↣ B) → (A ↣ C)
  B↔C ↣∘↣ A↔B  = record
    { to = to B↔C ∘ to A↔B 
    ; cong = cong B↔C ∘ cong A↔B 
    ; injective = injective A↔B ∘ injective B↔C
    }

  ↔-IsId : ∀ {A} → (R : A ↔ A) → Setω
  ↔-IsId {A} R = ∀ (a : A) → to R a ≡ a × a ≡ from R a
             
module _ {A B C D : Setω} where
  open Inverse

  ∘-assoc : (C→D : C → D) → (B→C : B → C) → (A→B : A → B)
          → (C→D ∘ B→C) ∘ A→B ≡ C→D ∘ (B→C ∘ A→B)
  ∘-assoc C→D B→C A→B = ≡.cong (λ _ x → C→D (B→C (A→B x))) ≡.refl

  ↔∘↔-assoc : (C↔D : C ↔ D) → (B↔C : B ↔ C) → (A↔B : A ↔ B)
            → (C↔D ↔∘↔ B↔C) ↔∘↔ A↔B ≡ C↔D ↔∘↔ (B↔C ↔∘↔ A↔B)
  ↔∘↔-assoc C↔D B↔C A↔B =
    begin
        (C↔D ↔∘↔ B↔C) ↔∘↔ A↔B
      ≡⟨ ≡.refl ⟩
        B↔D ↔∘↔ A↔B
      ≡⟨ ≡.refl ⟩
        A↔D₁
      ≡⟨ ≡.refl ⟩
        A↔D₂
      ≡⟨ ≡.refl ⟩
        C↔D ↔∘↔ A↔C 
      ≡⟨ ≡.refl ⟩
        C↔D ↔∘↔ (B↔C ↔∘↔ A↔B) ∎
    where
      A↔C : A ↔ C
      A↔C = record
        { to = to B↔C ∘ to A↔B
        ; from = from A↔B ∘ from B↔C
        ; to-cong = to-cong B↔C ∘ to-cong A↔B 
        ; from-cong = from-cong A↔B ∘ from-cong B↔C
        ; inverse = fst (inverse B↔C) ∘ fst (inverse A↔B)
                  , snd (inverse A↔B) ∘ snd (inverse B↔C)
        }
      B↔D : B ↔ D
      B↔D = record
        { to = to C↔D ∘ to B↔C
        ; from = from B↔C ∘ from C↔D
        ; to-cong = to-cong C↔D ∘ to-cong B↔C 
        ; from-cong = from-cong B↔C ∘ from-cong C↔D
        ; inverse = fst (inverse C↔D) ∘ fst (inverse B↔C)
                  , snd (inverse B↔C) ∘ snd (inverse C↔D)
        }
      A↔D₁ : A ↔ D
      A↔D₁ = record
        { to = (to C↔D ∘ to B↔C) ∘ to A↔B
        ; from = from A↔B ∘ (from B↔C ∘ from C↔D)
        ; to-cong = (to-cong C↔D ∘ to-cong B↔C) ∘ to-cong A↔B
        ; from-cong = from-cong A↔B ∘ (from-cong B↔C ∘ from-cong C↔D)
        ; inverse = (fst (inverse C↔D) ∘ fst (inverse B↔C)) ∘ fst (inverse A↔B)
                  , snd (inverse A↔B) ∘ (snd (inverse B↔C) ∘ snd (inverse C↔D))
        }
      A↔D₂ : A ↔ D
      A↔D₂ = record
        { to = to C↔D ∘ (to B↔C ∘ to A↔B)
        ; from = (from A↔B ∘ from B↔C) ∘ from C↔D
        ; to-cong = to-cong C↔D ∘ (to-cong B↔C ∘ to-cong A↔B)
        ; from-cong = (from-cong A↔B ∘ from-cong B↔C) ∘ from-cong C↔D
        ; inverse = fst (inverse C↔D) ∘ (fst (inverse B↔C) ∘ fst (inverse A↔B))
                  , (snd (inverse A↔B) ∘ snd (inverse B↔C)) ∘ snd (inverse C↔D)
        }

module _  where
  open Inverse

  double-flip : ∀ {A B} (R : A ↔ B) → (flip-↔ (flip-↔ R)) ≡ R
  double-flip R = ≡.refl
  
  flip-IsId : ∀ {A B} (R : A ↔ B) → ↔-IsId ((flip-↔ R) ↔∘↔ R)
  fst (flip-IsId {A} {B} R a) = snd (inverse R) {a} {to R a} ≡.refl
  snd (flip-IsId {A} {B} R a) =
    begin
        a
      ≡⟨ ≡.sym (fst (inverse (flip-↔ R)) ≡.refl) ⟩
        to (flip-↔ R) (from (flip-↔ R) a)
      ≡⟨ ≡.refl ⟩
        from R (to R a) ∎

module _ where
  open Inverse

  swap : ∀ {A B} → ⟦ A + B ⟧ ↔ ⟦ B + A ⟧
  swap = (flip-↔ +↔⊎) ↔∘↔ ⊎-swap-↔ ↔∘↔ +↔⊎

  swap-involutive : ∀ {A B : SomeFin} {x} → ↔-IsId (swap ↔∘↔ swap)
  swap-involutive {A} {B} {x} = flip-IsId swap

  inl-injective : ∀ {A} {x y : A} → inl x ≡ inl y → x ≡ y
  inl-injective ≡.refl = ≡.refl
  inr-injective : ∀ {A} {x y : A} → inr x ≡ inr y → x ≡ y
  inr-injective ≡.refl = ≡.refl

  map↣⊎ : ∀ {A B C D} → (A ↣ B) → (C ↣ D) → ((A ⊎ C) ↣ (B ⊎ D))
  map↣⊎ {A} {B} {C} {D} f g = record
    { to = h
    ; cong = ≡.cong h
    ; injective = inj
    }
    where open Injection
          h : (A ⊎ C) → (B ⊎ D)
          h (inl a) = inl (to f a)
          h (inr c) = inr (to g c)
          inj : ∀ {x y} → h x ≡ h y → x ≡ y
          inj {inl x} {inl y} =
            ≡.cong inl ∘ injective f ∘ inl-injective
          inj {inr x} {inr y} =
            ≡.cong inr ∘ injective g ∘ inr-injective

  id↣ : ∀ {A} → A ↣ A
  id↣ {A} = record
    { to = id
    ; cong = id
    ; injective = id
    }

  ⊎⊥ˡ : ∀ {A} → (A ⊎ ⟦ zero ⟧) ↔ A
  ⊎⊥ˡ {A} = record
    { to = f
    ; from = inl
    ; to-cong = f-cong
    ; from-cong = ≡.cong inl
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
      invʳ {inl x} {y} = ≡.cong inl
      
  ⊎⊥ʳ : ∀ {A} → (⟦ zero ⟧ ⊎ A) ↔ A
  ⊎⊥ʳ {A} = record
    { to = f
    ; from = inr
    ; to-cong = f-cong
    ; from-cong = ≡.cong inr
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
      invʳ {inr x} {y} = ≡.cong inr


module _ where
  open Injection 

  splice : {X : SomeFin} → (a : ⟦ suc X ⟧) → ⟦ X ⟧ ↔ (suc X ∖ a)
  splice {X} a = record
    { to = add a
    ; from = del a 
    ; to-cong = ≡.cong (add a)
    ; from-cong = ≡.cong (del a)
    ; inverse = {!!} , {!!}
    }

  splice-inverseˡ : {X : SomeFin} → (a : ⟦ suc X ⟧) → Inverseˡ _≡_ _≡_ (del a) (add a)
  splice-inverseˡ {zero} a {()} {y} y≡x+
  splice-inverseˡ {suc X} fzero {fzero} {fsuc y , y'≢0} y≡x+ = {!!}
  splice-inverseˡ {suc X} (fsuc a) {fzero} {fzero , 0≢a'} y≡x+ = ≡.refl
  splice-inverseˡ {suc X} fzero {fsuc x} {fsuc (fsuc y) , y≢0} =
    λ L → 
      {!!} ( ≡.cong inl L)
         
     -- ≡.cong fsuc {!suc-inj (suc-inj (inl-injective!} --  (≡.cong inl {!y≡x+!})
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
      g = map↣⊎ id↣ {!add!}  ↣∘↣ f ↣∘↣ map↣⊎ id↣ {!!}

  -- _-ᶠ_ {A'} {X} {Y} f A =
  --   let g = (↔to↣ (swap {Y} {A'})) ↣∘↣ f ↣∘↣ (↔to↣ (swap {A'} {X}))
  --   in sym-sub g A


  _+ᶠ-sym_ : ∀ {X Y : SomeFin} (g : ⟦ X ⟧ ↣ ⟦ Y ⟧) → (A : SomeFin)
          → ⟦ X + A ⟧ ↣ ⟦ Y + A ⟧
  _+ᶠ-sym_ {X} {Y} g A = ↔to↣ (flip-↔ +↔⊎) ↣∘↣ map↣⊎ g (id↣ {⟦ A ⟧}) ↣∘↣ ↔to↣ +↔⊎

{-
  _+ᶠ-sym_ : ∀ {X Y : SomeFin} (g : ⟦ X ⟧ ↣ ⟦ Y ⟧) → (A : SomeFin)
          → ⟦ A + X ⟧ ↣ ⟦ A + Y ⟧
  _+ᶠ-sym_ {X} {Y} g ℕ.zero = g
  _+ᶠ-sym_ {X} {Y} g (suc A) = ↔to↣ (flip-↔ +↔⊎) ↣∘↣ map↣⊎ (id↣ {⟦ 1 ⟧}) (g +ᶠ-sym A) ↣∘↣ ↔to↣ +↔⊎
-}
{-
    record
      { to = g''
      ; cong = ≡.cong g''
      ; injective = inj
      }
     where
       g' = g +ᶠ-sym A
       g'' : Fin (suc A + X) → Fin (suc A + Y)
       g'' fzero = fzero
       g'' (fsuc a) = fsuc (to g' a)
       inj : Injective _≡_ _≡_ g''
       inj {fzero} {fzero} eq = ≡.refl
       inj {fsuc x} {fsuc y} eq =
         begin
              fsuc x
            ≡⟨ ≡.cong fsuc (injective g' (suc-inj eq)) ⟩
              fsuc y ∎

_+ᶠ_ : ∀ {X Y : SomeFin} (g : Fin X ↣ Fin Y) → (A : SomeFin) → Fin (X + A) ↣ Fin (Y + A)
_+ᶠ_ {X} {Y} g A =
  subst (λ h → Fin (X + A) ↣ Fin h)
          (≡.sym (+-comm Y A))
    (subst (λ h → Fin h ↣ Fin (A + Y))
             (≡.sym (+-comm X A))
       (g +ᶠ-sym A))

_⊙_ : ∀ {X Y fzero} → (Fin Y ↣ Fin fzero) → (Fin X ↣ Fin Y) → (Fin X ↣ Fin fzero)
_⊙_ g f = record
  { to = to g ∘ to f 
  ; cong = cong g ∘ cong f
  ; injective = injective f ∘ injective g
  }

module theorem1-2 where
  private
    variable A B X Y fzero : SomeFin

  lemma1-3 : ∀ (f : Fin X ↣ Fin Y) → (f +ᶠ A) -ᶠ A ≡ f
  lemma1-3 {A = ℕ.zero} f = 
    begin
        f +ᶠ ℕ.zero -ᶠ ℕ.zero
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ {!!} ⟩
        f ∎

  lemma1-3 {A = suc A} f = {!!}

  --lemma1-3 : ∀ {X Y : SomeFin} → (f : Fin (X + 0) ↣ Fin (Y + 0)) → (f -ᶠ 0) ≡ f

  --lemma1 : ∀ {A X Y fzero} → (f : Fin (Y + A) ↣ Fin (fzero + A)) → (g : Fin X ↣ Fin Y) → (f ⊙ (g +ᶠ A)) -ᶠ A ≡ (f -ᶠ A) ⊙ g 
  --lemma1 {ℕ.zero} {X} {Y} {fzero} f g = 
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
