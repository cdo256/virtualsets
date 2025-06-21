module VirtualSet.Base where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Fin
  using (Fin) renaming (suc to sꟳ; zero to zꟳ)
open import Data.Fin.Properties
  using (_≟_; 0≢1+n; suc-injective; +↔⊎)
import Data.Nat.Properties
  using (+-comm; +-suc)
open import Data.Nat
  using (ℕ) renaming (_+_ to _+ℕ_; suc to sᴺ; zero to zᴺ)
open import Data.Product
  using (Σ; Σ-syntax; _×_; proj₁; proj₂)
open import Data.Product.Base as Product
  using (∃; _×_; _,_)
open import Data.Sum
  using (inj₁; inj₂; _⊎_) renaming (swap to ⊎-swap)
open import Data.Sum.Properties
  using () renaming (swap-↔ to ⊎-swap-↔)
open import Level
  using (_⊔_; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.Structures
  using (IsEquivalence)
import Relation.Binary.PropositionalEquality.Core as ≡
  using (refl; sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_)
open import Relation.Binary.Reasoning.Syntax
  using (module ≡-syntax)
open import Relation.Nullary.Decidable as Dec
  using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
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

open ≡-Reasoning
private
  variable
    c ℓ : Level.Level

SomeFin : Set
SomeFin = ℕ

⟦_⟧ : (n : SomeFin) → Set
⟦ n ⟧ = Fin n

_∖_ : (A : SomeFin) → (a : Fin A) → Set
A ∖ a = Σ[ b ∈ Fin A ] a ≢ b

add : {x : ℕ} → (a : ⟦ sᴺ x ⟧) → ⟦ x ⟧ → (sᴺ x ∖  a) 
add {sᴺ x} zꟳ b = sꟳ b , λ ()
add {sᴺ x} (sꟳ a) zꟳ = zꟳ , λ ()
add {sᴺ x} (sꟳ a) (sꟳ b) =
  let
    (c , a≢c) = add a b
  in sꟳ (proj₁ (add a b)) , λ a'≡c' → a≢c (suc-injective a'≡c')

del : {x : ℕ} → (a : ⟦ sᴺ x ⟧) → (sᴺ x ∖ a) → ⟦ x ⟧
del {ℕ.zero} zꟳ (zꟳ , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {sᴺ x} zꟳ (zꟳ , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {sᴺ x} zꟳ (sꟳ b , a≢b) = b
del {sᴺ x} (sꟳ a) (zꟳ , a≢b) = zꟳ
del {sᴺ x} (sꟳ a) (sꟳ b , a'≢b') =
  sꟳ (del {x} a (b , λ a≡b → ⊥-elim (a'≢b' (≡.cong sꟳ a≡b))))

del-zero-suc : ∀ {x} (b : ⟦ x ⟧) (a≢b : zꟳ ≢ sꟳ b) → del zꟳ (sꟳ b , a≢b) ≡ b
del-zero-suc b a≢b with del zꟳ (sꟳ b , a≢b) | inspect (del zꟳ) (sꟳ b , a≢b)
... | zꟳ | [ eq ] = ≡.sym eq
... | sꟳ X | [ eq ] = ≡.sym eq

del-inj : {x : ℕ} → (a : ⟦ sᴺ x ⟧)
        → (B₁ B₂ : (sᴺ x ∖ a))
        → del a B₁ ≡ del a B₂
        → proj₁ B₁ ≡ proj₁ B₂
del-inj zꟳ (zꟳ , a≢b₁) (zꟳ , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj zꟳ (zꟳ , a≢b₁) (sꟳ b₂ , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj zꟳ (sꟳ b₁ , a≢b₁) (zꟳ , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₂ ≡.refl)
del-inj zꟳ (sꟳ b₁ , a≢b₁) (sꟳ b₂ , a≢b₂) b₁'≡b₂' =
  let b₁' = del zꟳ (sꟳ b₁ , a≢b₁)
      b₂' = del zꟳ (sꟳ b₂ , a≢b₂)
      b₁'≡b₁ : b₁' ≡ b₁
      b₁'≡b₁ = del-zero-suc b₁ a≢b₁
      b₂'≡b₂ : b₂' ≡ b₂
      b₂'≡b₂ = del-zero-suc b₂ a≢b₂
  in begin
      sꟳ b₁
    ≡⟨ ≡.cong sꟳ (≡.sym b₁'≡b₁) ⟩
      sꟳ b₁'
    ≡⟨ ≡.cong sꟳ b₁'≡b₂' ⟩
      sꟳ b₂'
    ≡⟨ ≡.cong sꟳ b₂'≡b₂ ⟩
      sꟳ b₂ ∎
del-inj (sꟳ a) (zꟳ , a≢b₁) (zꟳ , a≢b₂) b₁'≡b₂' = ≡.refl
del-inj (sꟳ a) (zꟳ , a≢b₁) (sꟳ b₂ , a≢b₂) b₁'≡b₂'
  with del (sꟳ a) (zꟳ , a≢b₁) | inspect (del (sꟳ a)) (zꟳ , a≢b₁) | del (sꟳ a) (sꟳ b₂  , a≢b₂) | inspect (del (sꟳ a)) (sꟳ b₂ , a≢b₂)
... | zꟳ | [ eq₁ ] | zꟳ | ()
... | zꟳ | _ | sꟳ _ | _ = ⊥-elim (0≢1+n b₁'≡b₂')
... | sꟳ X | () | _ | _
del-inj (sꟳ a) (sꟳ b₁ , a≢b₁) (zꟳ , a≢b₂) b₁'≡b₂' =
  ≡.sym (del-inj (sꟳ a) (zꟳ , a≢b₂) (sꟳ b₁ , a≢b₁) (≡.sym b₁'≡b₂'))
del-inj (sꟳ a) (sꟳ b₁ , sa≢sb₁) (sꟳ b₂ , sa≢sb₂) b₁'≡b₂'
  with del (sꟳ a) (sꟳ b₁ , sa≢sb₁) | inspect (del (sꟳ a)) (sꟳ b₁ , sa≢sb₁) | del (sꟳ a) (sꟳ b₂  , sa≢sb₂) | inspect (del (sꟳ a)) (sꟳ b₂ , sa≢sb₂) | b₁'≡b₂'
... | sꟳ c₁ | [ eq₁ ] | sꟳ c₂ | [ eq₂ ] | _ =
  ≡.cong sꟳ (del-inj a (b₁ , λ a≡b₁ → sa≢sb₁ (≡.cong sꟳ a≡b₁))
                      (b₂ , λ a≡b₂ → sa≢sb₂ (≡.cong sꟳ a≡b₂))
                      (suc-injective b₁'≡b₂'))

add-inj : {x : ℕ} → (a : ⟦ sᴺ x ⟧)
        → (b₁ b₂ : Fin x)
        → proj₁ (add a b₁) ≡ proj₁ (add a b₂)
        → b₁ ≡ b₂
add-inj zꟳ zꟳ zꟳ c₁≡c₂ = ≡.refl
add-inj zꟳ (sꟳ b₁) (sꟳ b₂) c₁≡c₂
  with add zꟳ b₁ | inspect (add zꟳ) b₁ | add zꟳ b₂ | inspect (add zꟳ) b₂
... | c₁ , z≢c₁ | [ eq₁ ] | c₂ , z≢c₂ | [ eq₂ ] = suc-injective c₁≡c₂
add-inj (sꟳ a) zꟳ zꟳ c₁≡c₂ = ≡.refl
add-inj (sꟳ a) (sꟳ b₁) (sꟳ b₂) c₁≡c₂
  with add (sꟳ a) (sꟳ b₁) | inspect (add (sꟳ a)) (sꟳ b₁) | add (sꟳ a) (sꟳ b₂) | inspect (add (sꟳ a)) (sꟳ b₂)
... | sꟳ c₁ , sa≢sc₁ | [ eq₁ ] | sꟳ c₂ , sa≢sc₂ | [ eq₂ ] =
  ≡.cong sꟳ (add-inj a b₁ b₂ (suc-injective c₁≡c₂))

module _ {x y : ℕ} (f : ⟦ sᴺ x ⟧ ↣ ⟦ sᴺ y ⟧) where
  open Injection

  f' : Fin x → Fin y
  f' i =
    let (j , 0≢j) = add zꟳ i 
    in del (to f zꟳ) (to f j , λ f0≡fj → 0≢j (injective f f0≡fj))

  comp : (ai : (b₁ b₂ : ⟦ x ⟧) → proj₁ (add zꟳ b₁) ≡ proj₁ (add zꟳ b₂) → b₁ ≡ b₂)
       → (di : (B₁ B₂ : (sᴺ y) ∖ to f zꟳ)
             → del (to f zꟳ) B₁ ≡ del (to f zꟳ) B₂ → proj₁ B₁ ≡ proj₁ B₂)
       → Injective _≡_ _≡_ f'
  comp ai di {b₁} {b₂} f'b₁≡f'b₂ =
    let
      (c₁ , z≢c₁) = add zꟳ b₁
      (c₂ , z≢c₂) = add zꟳ b₂
    in
    ai b₁ b₂
       (injective f {c₁} {c₂}
            (di (to f c₁ , λ fz≡fc₁ → z≢c₁ (injective f {zꟳ} {c₁} fz≡fc₁))
                (to f c₂ , λ fz≡fc₂ → z≢c₂ (injective f {zꟳ} {c₂} fz≡fc₂))
                f'b₁≡f'b₂))

  sub : ⟦ x ⟧ ↣ ⟦ y ⟧
  sub = record
    { to = f'
    ; cong = ≡.cong f'
    ; injective = comp (add-inj zꟳ) (del-inj (to f zꟳ))
    }

infixl 6 _+_ _+ᶠ_ _-ᶠ_
_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y

sym-sub : {A' X Y : SomeFin} → (f : ⟦ A' + X ⟧ ↣ ⟦ A' + Y ⟧)
    → (A : SomeFin) → {A ≡ A'}
    → ⟦ X ⟧ ↣ ⟦ Y ⟧
sym-sub {ℕ.zero} {X} {Y} f ℕ.zero = f
sym-sub {sᴺ A'} {X} {Y} f (sᴺ A) = (sym-sub (sub f) A)

+-comm : ∀ (A B : SomeFin) → A + B ≡ B + A
+-comm = Data.Nat.Properties.+-comm

+-identityʳ : ∀ (x : SomeFin) → x + ℕ.zero ≡ x
+-identityʳ ℕ.zero = ≡.refl
+-identityʳ (sᴺ n) =
  ≡.cong sᴺ (+-identityʳ n)


module _ {A B C D : Set} where
  open Inverse
  flip-↔ : (A ↔ B) → (B ↔ A)
  flip-↔ A↔B = record
    { to = from A↔B
    ; from = to A↔B
    ; to-cong = from-cong A↔B
    ; from-cong = to-cong A↔B
    ; inverse = (proj₂ (inverse A↔B)) , (proj₁ (inverse A↔B))
    }

  infixl 9 _↔∘↔_

  _↔∘↔_ : (B ↔ C) → (A ↔ B) → (A ↔ C)
  B↔C ↔∘↔ A↔B  = record
    { to = to B↔C ∘ to A↔B 
    ; from = from A↔B ∘ from B↔C
    ; to-cong = to-cong B↔C ∘ to-cong A↔B 
    ; from-cong = from-cong A↔B ∘ from-cong B↔C 
    ; inverse = proj₁ (inverse B↔C) ∘ proj₁ (inverse A↔B)
              , proj₂ (inverse A↔B) ∘ proj₂ (inverse B↔C) }

  ↔-IsId : ∀ {A} → (R : A ↔ A) → Set _
  ↔-IsId {A} R = ∀ (a : A) → to R a ≡ a × a ≡ from R a
             
module _ {A B C D : Set} where
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
        ; inverse = proj₁ (inverse B↔C) ∘ proj₁ (inverse A↔B)
                  , proj₂ (inverse A↔B) ∘ proj₂ (inverse B↔C)
        }
      B↔D : B ↔ D
      B↔D = record
        { to = to C↔D ∘ to B↔C
        ; from = from B↔C ∘ from C↔D
        ; to-cong = to-cong C↔D ∘ to-cong B↔C 
        ; from-cong = from-cong B↔C ∘ from-cong C↔D
        ; inverse = proj₁ (inverse C↔D) ∘ proj₁ (inverse B↔C)
                  , proj₂ (inverse B↔C) ∘ proj₂ (inverse C↔D)
        }
      A↔D₁ : A ↔ D
      A↔D₁ = record
        { to = (to C↔D ∘ to B↔C) ∘ to A↔B
        ; from = from A↔B ∘ (from B↔C ∘ from C↔D)
        ; to-cong = (to-cong C↔D ∘ to-cong B↔C) ∘ to-cong A↔B
        ; from-cong = from-cong A↔B ∘ (from-cong B↔C ∘ from-cong C↔D)
        ; inverse = (proj₁ (inverse C↔D) ∘ proj₁ (inverse B↔C)) ∘ proj₁ (inverse A↔B)
                  , proj₂ (inverse A↔B) ∘ (proj₂ (inverse B↔C) ∘ proj₂ (inverse C↔D))
        }
      A↔D₂ : A ↔ D
      A↔D₂ = record
        { to = to C↔D ∘ (to B↔C ∘ to A↔B)
        ; from = (from A↔B ∘ from B↔C) ∘ from C↔D
        ; to-cong = to-cong C↔D ∘ (to-cong B↔C ∘ to-cong A↔B)
        ; from-cong = (from-cong A↔B ∘ from-cong B↔C) ∘ from-cong C↔D
        ; inverse = proj₁ (inverse C↔D) ∘ (proj₁ (inverse B↔C) ∘ proj₁ (inverse A↔B))
                  , (proj₂ (inverse A↔B) ∘ proj₂ (inverse B↔C)) ∘ proj₂ (inverse C↔D)
        }

module _  where
  open Inverse

  double-flip : ∀ {A B} (R : A ↔ B) → (flip-↔ (flip-↔ R)) ≡ R
  double-flip R = ≡.refl

  flip-IsId : ∀ {A B} (R : A ↔ B) → ↔-IsId ((flip-↔ R) ↔∘↔ R)
  proj₁ (flip-IsId {A} {B} R a) = proj₂ (inverse R) {a} {to R a} ≡.refl
  proj₂ (flip-IsId {A} {B} R a) =
    begin
        a
      ≡⟨ ≡.sym (proj₁ (inverse (flip-↔ R)) ≡.refl) ⟩
        to (flip-↔ R) (from (flip-↔ R) a)
      ≡⟨ ≡.refl ⟩
        from R (to R a) ∎

module _ where
  open Inverse

  swap : ∀ {A B} → ⟦ A + B ⟧ ↔ ⟦ B + A ⟧
  swap = (flip-↔ +↔⊎) ↔∘↔ ⊎-swap-↔ ↔∘↔ +↔⊎

  swap-involutive : ∀ {A B : SomeFin} {x} → ↔-IsId (swap ↔∘↔ swap)
  swap-involutive {A} {B} {x} = flip-IsId {!swap!}

-- swap-involutive : ∀ {A B} → Inverseˡ _≡_ _≡_ (swap {B} {A}) (swap {A} {B})
-- swap-involutive {A} {B} {x} {y} = {!inv!}
--   where inv : ∀ {A B x} → swap {B} {A} (swap {A} {B} x) ≡ x
--         inv {ℕ.zero} {sᴺ B} {zꟳ} = 
--           begin
--               swap (swap zꟳ)
--             ≡⟨ ≡.refl ⟩
--               swap {sᴺ B} {ℕ.zero} (swap {ℕ.zero} {sᴺ B} zꟳ)
--             ≡⟨ ≡.cong swap ≡.refl ⟩
--               swap {sᴺ B} {ℕ.zero} (≡.subst Fin (+-comm ℕ.zero (sᴺ B)) zꟳ)
--             ≡⟨ {!!} ⟩
--               {!!}
--             ≡⟨ {!!} ⟩
--               zꟳ ∎
--         inv {ℕ.zero} {sᴺ B} {sꟳ x} = {!!}
--         inv {sᴺ A} {B} {x} = {!!}
{-
commutate : ∀ {A B : SomeFin} → Fin (A + B) ↣ Fin (B + A)
commutate {A} {B} = record
  { to = f
  ; cong = λ eq → ≡.refl
  ; injective = λ {x} {y} eq → {!!}
  }
  where
    f : ∀ {A B} → Fin (A + B) → Fin (B + A)
    f {ℕ.zero} {B} x =
      ≡.subst Fin (+-comm ℕ.zero B) x
    f {sᴺ A} {ℕ.zero} x =
      ≡.subst Fin (+-comm (sᴺ A) ℕ.zero) x
    f {sᴺ A} {sᴺ B} zꟳ = sꟳ (f {sᴺ A} {B} zꟳ)
    f {sᴺ A} {sᴺ B} (sꟳ x) =
      sꟳ (f {sᴺ A} {B}
           (≡.subst Fin (Data.Nat.Properties.+-suc A B) x))
    inj : ∀ {A B} → Injective _≡_ _≡_ (f {A} {B})
    inj {ℕ.zero} {sᴺ B} {x} {y} fx≡fy = {!!}
    inj {sᴺ A} {ℕ.zero} {x} {y} fx≡fy = {!!}
    inj {sᴺ A} {sᴺ B} {x} {y} fx≡fy = {!!}

_-ᶠ_ : {A' X Y : SomeFin} → (f : Fin (X + A') ↣ Fin (Y + A'))
    → (A : SomeFin) → {A ≡ A'}
    → Fin X ↣ Fin Y
_-ᶠ_ {A'} {X} {Y} f A =
  sym-sub (≡.subst (λ h → Fin (A' + X) ↣ Fin h) (+-comm Y A') (≡.subst (λ h → Fin h ↣ Fin (Y + A')) (+-comm X A') f)) A

-- ≡.subst (λ h → Fin (X + ℕ.zero) ↣ Fin h)
--         (≡.sym (+-identityʳ Y))
--   (≡.subst (λ h → Fin h ↣ Fin Y)
--            (≡.sym (+-identityʳ X))


_+ᶠ-sym_ : ∀ {X Y : SomeFin} (g : Fin X ↣ Fin Y) → (A : SomeFin) → Fin (A + X) ↣ Fin (A + Y)
_+ᶠ-sym_ {X} {Y} g ℕ.zero = g
_+ᶠ-sym_ {X} {Y} g (sᴺ A) =
    record
      { to = g''
      ; cong = ≡.cong g''
      ; injective = inj
      }
     where
       g' = g +ᶠ-sym A
       g'' : Fin (sᴺ A + X) → Fin (sᴺ A + Y)
       g'' zꟳ = zꟳ
       g'' (sꟳ a) = sꟳ (to g' a)
       inj : Injective _≡_ _≡_ g''
       inj {zꟳ} {zꟳ} eq = ≡.refl
       inj {sꟳ x} {sꟳ y} eq =
         begin
              sꟳ x
            ≡⟨ ≡.cong sꟳ (injective g' (suc-injective eq)) ⟩
              sꟳ y ∎

_+ᶠ_ : ∀ {X Y : SomeFin} (g : Fin X ↣ Fin Y) → (A : SomeFin) → Fin (X + A) ↣ Fin (Y + A)
_+ᶠ_ {X} {Y} g A =
  ≡.subst (λ h → Fin (X + A) ↣ Fin h)
          (≡.sym (+-comm Y A))
    (≡.subst (λ h → Fin h ↣ Fin (A + Y))
             (≡.sym (+-comm X A))
       (g +ᶠ-sym A))

_⊙_ : ∀ {X Y zꟳ} → (Fin Y ↣ Fin zꟳ) → (Fin X ↣ Fin Y) → (Fin X ↣ Fin zꟳ)
_⊙_ g f = record
  { to = to g ∘ to f 
  ; cong = cong g ∘ cong f
  ; injective = injective f ∘ injective g
  }

module theorem1-2 where
  private
    variable A B X Y zꟳ : SomeFin

  lemma1-3 : ∀ (f : Fin X ↣ Fin Y) → (f +ᶠ A) -ᶠ A ≡ f
  lemma1-3 {A = ℕ.zero} f = 
    begin
        f +ᶠ ℕ.zero -ᶠ ℕ.zero
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ {!!} ⟩
        f ∎

  lemma1-3 {A = sᴺ A} f = {!!}

  --lemma1-3 : ∀ {X Y : SomeFin} → (f : Fin (X + 0) ↣ Fin (Y + 0)) → (f -ᶠ 0) ≡ f

  --lemma1 : ∀ {A X Y zꟳ} → (f : Fin (Y + A) ↣ Fin (zꟳ + A)) → (g : Fin X ↣ Fin Y) → (f ⊙ (g +ᶠ A)) -ᶠ A ≡ (f -ᶠ A) ⊙ g 
  --lemma1 {ℕ.zero} {X} {Y} {zꟳ} f g = 
  --  begin
  --      ((f ⊙ (g +ᶠ 0)) -ᶠ 0)
  --    ≡⟨ {!!} ⟩
  --      {!!}
  --    ≡⟨ {!!} ⟩
  --      ((f -ᶠ 0) ⊙ g ) ∎

  --lemma1 {sᴺ A} {X} {Y} {zꟳ} f g = {!!}
  --  -- begin
  --  --     ((f ⊙ (g +ᶠ A)) -ᶠ A)
  --  --   ≡⟨ {!!} ⟩
  --  --     ((f -ᶠ A) ⊙ g ) ∎
-- -}
