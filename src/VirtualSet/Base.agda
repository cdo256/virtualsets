module VirtualSet.Base where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Fin
  using (Fin) renaming (suc to s; zero to z)
open import Data.Fin.Properties
  using (_≟_; 0≢1+n; suc-injective; +↔⊎)
import Data.Nat.Properties
  using (+-comm; +-suc)
open import Data.Nat
  using (ℕ) renaming (_+_ to _+ℕ_)
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
  using (_↣_; _↔_; Injection)
open import Algebra.Definitions
  using (RightIdentity)
open import Function.Definitions
  using (Injective; Congruent;
         Inverseˡ; Inverseʳ; Inverseᵇ)


open ≡-Reasoning
private
  variable
    c ℓ : Level.Level

add : {x : ℕ} → (a : Fin (ℕ.suc x)) → (b : Fin x) → (Σ[ c ∈ Fin (ℕ.suc x) ] a ≢ c)
add {ℕ.suc x} z b = s b , λ ()
add {ℕ.suc x} (s a) z = z , λ ()
add {ℕ.suc x} (s a) (s b) =
  let
    (c , a≢c) = add a b
  in s (proj₁ (add a b)) , λ a'≡c' → a≢c (suc-injective a'≡c')

del : {x : ℕ} → (a : Fin (ℕ.suc x)) → (Σ[ b ∈ Fin (ℕ.suc x) ] a ≢ b) → Fin x
del {ℕ.zero} z (z , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} z (z , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} z (s b , a≢b) = b
del {ℕ.suc x} (s a) (z , a≢b) = z
del {ℕ.suc x} (s a) (s b , a'≢b') =
  s (del {x} a (b , λ a≡b → ⊥-elim (a'≢b' (≡.cong s a≡b))))

del-zero-suc : ∀ {x} (b : Fin x) (a≢b : z ≢ s b) → del z (s b , a≢b) ≡ b
del-zero-suc b a≢b with del z (s b , a≢b) | inspect (del z) (s b , a≢b)
... | z | [ eq ] = ≡.sym eq
... | s X | [ eq ] = ≡.sym eq

del-inj : {x : ℕ} → (a : Fin (ℕ.suc x))
        → (B₁ B₂ : Σ[ b ∈ Fin (ℕ.suc x) ] a ≢ b)
        → del a B₁ ≡ del a B₂
        → proj₁ B₁ ≡ proj₁ B₂
del-inj z (z , a≢b₁) (z , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj z (z , a≢b₁) (s b₂ , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj z (s b₁ , a≢b₁) (z , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₂ ≡.refl)
del-inj z (s b₁ , a≢b₁) (s b₂ , a≢b₂) b₁'≡b₂' =
  let b₁' = del z (s b₁ , a≢b₁)
      b₂' = del z (s b₂ , a≢b₂)
      b₁'≡b₁ : b₁' ≡ b₁
      b₁'≡b₁ = del-zero-suc b₁ a≢b₁
      b₂'≡b₂ : b₂' ≡ b₂
      b₂'≡b₂ = del-zero-suc b₂ a≢b₂
  in begin
      s b₁
    ≡⟨ ≡.cong s (≡.sym b₁'≡b₁) ⟩
      s b₁'
    ≡⟨ ≡.cong s b₁'≡b₂' ⟩
      s b₂'
    ≡⟨ ≡.cong s b₂'≡b₂ ⟩
      s b₂ ∎
del-inj (s a) (z , a≢b₁) (z , a≢b₂) b₁'≡b₂' = ≡.refl
del-inj (s a) (z , a≢b₁) (s b₂ , a≢b₂) b₁'≡b₂'
  with del (s a) (z , a≢b₁) | inspect (del (s a)) (z , a≢b₁) | del (s a) (s b₂  , a≢b₂) | inspect (del (s a)) (s b₂ , a≢b₂)
... | z | [ eq₁ ] | z | ()
... | z | _ | s _ | _ = ⊥-elim (0≢1+n b₁'≡b₂')
... | s X | () | _ | _
del-inj (s a) (s b₁ , a≢b₁) (z , a≢b₂) b₁'≡b₂' =
  ≡.sym (del-inj (s a) (z , a≢b₂) (s b₁ , a≢b₁) (≡.sym b₁'≡b₂'))
del-inj (s a) (s b₁ , sa≢sb₁) (s b₂ , sa≢sb₂) b₁'≡b₂'
  with del (s a) (s b₁ , sa≢sb₁) | inspect (del (s a)) (s b₁ , sa≢sb₁) | del (s a) (s b₂  , sa≢sb₂) | inspect (del (s a)) (s b₂ , sa≢sb₂) | b₁'≡b₂'
... | s c₁ | [ eq₁ ] | s c₂ | [ eq₂ ] | _ =
  ≡.cong s (del-inj a (b₁ , λ a≡b₁ → sa≢sb₁ (≡.cong s a≡b₁))
                      (b₂ , λ a≡b₂ → sa≢sb₂ (≡.cong s a≡b₂))
                      (suc-injective b₁'≡b₂'))

add-inj : {x : ℕ} → (a : Fin (ℕ.suc x))
        → (b₁ b₂ : Fin x)
        → proj₁ (add a b₁) ≡ proj₁ (add a b₂)
        → b₁ ≡ b₂
add-inj z z z c₁≡c₂ = ≡.refl
add-inj z (s b₁) (s b₂) c₁≡c₂
  with add z b₁ | inspect (add z) b₁ | add z b₂ | inspect (add z) b₂
... | c₁ , z≢c₁ | [ eq₁ ] | c₂ , z≢c₂ | [ eq₂ ] = suc-injective c₁≡c₂
add-inj (s a) z z c₁≡c₂ = ≡.refl
add-inj (s a) (s b₁) (s b₂) c₁≡c₂
  with add (s a) (s b₁) | inspect (add (s a)) (s b₁) | add (s a) (s b₂) | inspect (add (s a)) (s b₂)
... | s c₁ , sa≢sc₁ | [ eq₁ ] | s c₂ , sa≢sc₂ | [ eq₂ ] =
  ≡.cong s (add-inj a b₁ b₂ (suc-injective c₁≡c₂))

SomeFin : Set
SomeFin = ℕ

_∖_ : (A : SomeFin) → (a : Fin A) → Set
A ∖ a = Σ[ b ∈ Fin A ] a ≢ b


module _ {x y : ℕ} (f : Fin (ℕ.suc x) ↣ Fin (ℕ.suc y)) where
  open Injection

  f' : Fin x → Fin y
  f' i =
    let (j , 0≢j) = add z i 
    in del (to f z) (to f j , λ f0≡fj → 0≢j (injective f f0≡fj))

  comp : (ai : (b₁ b₂ : Fin x) → proj₁ (add z b₁) ≡ proj₁ (add z b₂) → b₁ ≡ b₂)
       → (di : (B₁ B₂ : (ℕ.suc y) ∖ to f z)
             → del (to f z) B₁ ≡ del (to f z) B₂ → proj₁ B₁ ≡ proj₁ B₂)
       → Injective _≡_ _≡_ f'
  comp ai di {b₁} {b₂} f'b₁≡f'b₂ =
    let
      (c₁ , z≢c₁) = add z b₁
      (c₂ , z≢c₂) = add z b₂
    in
    ai b₁ b₂
       (injective f {c₁} {c₂}
            (di (to f c₁ , λ fz≡fc₁ → z≢c₁ (injective f {z} {c₁} fz≡fc₁))
                (to f c₂ , λ fz≡fc₂ → z≢c₂ (injective f {z} {c₂} fz≡fc₂))
                f'b₁≡f'b₂))

  sub : Fin x ↣ Fin y
  sub = record
    { to = f'
    ; cong = ≡.cong f'
    ; injective = comp (add-inj z) (del-inj (to f z))
    }

infixl 6 _+_ _+ᶠ_ _-ᶠ_
_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y

sym-sub : {A' X Y : SomeFin} → (f : Fin (A' + X) ↣ Fin (A' + Y))
    → (A : SomeFin) → {A ≡ A'}
    → Fin X ↣ Fin Y
sym-sub {ℕ.zero} {X} {Y} f ℕ.zero = f
sym-sub {ℕ.suc A'} {X} {Y} f (ℕ.suc A) = (sym-sub (sub f) A)

+-comm : ∀ (A B : SomeFin) → A + B ≡ B + A
+-comm = Data.Nat.Properties.+-comm

+-identityʳ : ∀ (x : SomeFin) → x + ℕ.zero ≡ x
+-identityʳ ℕ.zero = ≡.refl
+-identityʳ (ℕ.suc n) =
  ≡.cong ℕ.suc (+-identityʳ n)

swap : ∀ {A B} → Fin (A + B) → Fin (B + A)
swap {A} {B} =
  let foo = +↔⊎
  in {!!} ∘ {!!}


-- swap : ∀ {A B} → Fin (A + B) → Fin (B + A)
-- swap {ℕ.zero} {B} x =
--   ≡.subst Fin (+-comm ℕ.zero B) x
-- swap {ℕ.suc A} {ℕ.zero} x =
--   ≡.subst Fin (+-comm (ℕ.suc A) ℕ.zero) x
-- swap {ℕ.suc A} {ℕ.suc B} z = s (swap {ℕ.suc A} {B} z)
-- swap {ℕ.suc A} {ℕ.suc B} (s x) =
--   s (swap {ℕ.suc A} {B}
--           (≡.subst Fin (Data.Nat.Properties.+-suc A B) x))

-- swap-involutive : ∀ {A B} → Inverseˡ _≡_ _≡_ (swap {B} {A}) (swap {A} {B})
-- swap-involutive {A} {B} {x} {y} = {!inv!}
--   where inv : ∀ {A B x} → swap {B} {A} (swap {A} {B} x) ≡ x
--         inv {ℕ.zero} {ℕ.suc B} {z} = 
--           begin
--               swap (swap z)
--             ≡⟨ ≡.refl ⟩
--               swap {ℕ.suc B} {ℕ.zero} (swap {ℕ.zero} {ℕ.suc B} z)
--             ≡⟨ ≡.cong swap ≡.refl ⟩
--               swap {ℕ.suc B} {ℕ.zero} (≡.subst Fin (+-comm ℕ.zero (ℕ.suc B)) z)
--             ≡⟨ {!!} ⟩
--               {!!}
--             ≡⟨ {!!} ⟩
--               z ∎
--         inv {ℕ.zero} {ℕ.suc B} {s x} = {!!}
--         inv {ℕ.suc A} {B} {x} = {!!}

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
    f {ℕ.suc A} {ℕ.zero} x =
      ≡.subst Fin (+-comm (ℕ.suc A) ℕ.zero) x
    f {ℕ.suc A} {ℕ.suc B} z = s (f {ℕ.suc A} {B} z)
    f {ℕ.suc A} {ℕ.suc B} (s x) =
      s (f {ℕ.suc A} {B}
           (≡.subst Fin (Data.Nat.Properties.+-suc A B) x))
    inj : ∀ {A B} → Injective _≡_ _≡_ (f {A} {B})
    inj {ℕ.zero} {ℕ.suc B} {x} {y} fx≡fy = {!!}
    inj {ℕ.suc A} {ℕ.zero} {x} {y} fx≡fy = {!!}
    inj {ℕ.suc A} {ℕ.suc B} {x} {y} fx≡fy = {!!}

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
_+ᶠ-sym_ {X} {Y} g (ℕ.suc A) =
    record
      { to = g''
      ; cong = ≡.cong g''
      ; injective = inj
      }
     where
       g' = g +ᶠ-sym A
       g'' : Fin (ℕ.suc A + X) → Fin (ℕ.suc A + Y)
       g'' z = z
       g'' (s a) = s (to g' a)
       inj : Injective _≡_ _≡_ g''
       inj {z} {z} eq = ≡.refl
       inj {s x} {s y} eq =
         begin
              s x
            ≡⟨ ≡.cong s (injective g' (suc-injective eq)) ⟩
              s y ∎

_+ᶠ_ : ∀ {X Y : SomeFin} (g : Fin X ↣ Fin Y) → (A : SomeFin) → Fin (X + A) ↣ Fin (Y + A)
_+ᶠ_ {X} {Y} g A =
  ≡.subst (λ h → Fin (X + A) ↣ Fin h)
          (≡.sym (+-comm Y A))
    (≡.subst (λ h → Fin h ↣ Fin (A + Y))
             (≡.sym (+-comm X A))
       (g +ᶠ-sym A))

_⊙_ : ∀ {X Y Z} → (Fin Y ↣ Fin Z) → (Fin X ↣ Fin Y) → (Fin X ↣ Fin Z)
_⊙_ g f = record
  { to = to g ∘ to f 
  ; cong = cong g ∘ cong f
  ; injective = injective f ∘ injective g
  }

module theorem1-2 where
  private
    variable A B X Y Z : SomeFin

  lemma1-3 : ∀ (f : Fin X ↣ Fin Y) → (f +ᶠ A) -ᶠ A ≡ f
  lemma1-3 {A = ℕ.zero} f = 
    begin
        f +ᶠ ℕ.zero -ᶠ ℕ.zero
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ {!!} ⟩
        f ∎

  lemma1-3 {A = ℕ.suc A} f = {!!}

  --lemma1-3 : ∀ {X Y : SomeFin} → (f : Fin (X + 0) ↣ Fin (Y + 0)) → (f -ᶠ 0) ≡ f

  --lemma1 : ∀ {A X Y Z} → (f : Fin (Y + A) ↣ Fin (Z + A)) → (g : Fin X ↣ Fin Y) → (f ⊙ (g +ᶠ A)) -ᶠ A ≡ (f -ᶠ A) ⊙ g 
  --lemma1 {ℕ.zero} {X} {Y} {Z} f g = 
  --  begin
  --      ((f ⊙ (g +ᶠ 0)) -ᶠ 0)
  --    ≡⟨ {!!} ⟩
  --      {!!}
  --    ≡⟨ {!!} ⟩
  --      ((f -ᶠ 0) ⊙ g ) ∎

  --lemma1 {ℕ.suc A} {X} {Y} {Z} f g = {!!}
  --  -- begin
  --  --     ((f ⊙ (g +ᶠ A)) -ᶠ A)
  --  --   ≡⟨ {!!} ⟩
  --  --     ((f -ᶠ A) ⊙ g ) ∎
