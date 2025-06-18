module VirtualSet.Base where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Fin
  using (Fin)
open import Data.Fin.Properties
  using (_≟_)
open import Data.Nat
  using (ℕ; _+_)
open import Data.Product
  using (Σ-syntax; _×_; proj₁; proj₂)
open import Data.Product.Base as Product
  using (∃; _×_; _,_)
open import Data.Sum
  using (inj₁; inj₂)
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


open ≡-Reasoning

private
  variable
    c ℓ : Level.Level

injective : {X Y : Set} → (f : X → Y) → Set
injective {X} {Y} f = ∀ (a b : X) → f a ≡ f b → a ≡ b

module _ {x : ℕ} where

suc-injective : ∀ {w : ℕ} → injective {X = Fin w} Fin.suc
suc-injective _ _ ≡.refl = ≡.refl

add : {x : ℕ} → (a : Fin (ℕ.suc x)) → (b : Fin x) → (Σ[ c ∈ Fin (ℕ.suc x) ] a ≢ c)
add {ℕ.suc x} Fin.zero b = Fin.suc b , λ ()
add {ℕ.suc x} (Fin.suc a) Fin.zero = Fin.zero , λ ()
add {ℕ.suc x} (Fin.suc a) (Fin.suc b) =
  let
    (c , a≢c) = add a b
  in Fin.suc (proj₁ (add a b)) , λ a'≡c' → a≢c (suc-injective a c a'≡c')

del : {x : ℕ} → (a : Fin (ℕ.suc x)) → (Σ[ b ∈ Fin (ℕ.suc x) ] a ≢ b) → Fin x
del {ℕ.zero} Fin.zero (Fin.zero , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} Fin.zero (Fin.zero , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} Fin.zero (Fin.suc b , a≢b) = b
del {ℕ.suc x} (Fin.suc a) (Fin.zero , a≢b) = Fin.zero
del {ℕ.suc x} (Fin.suc a) (Fin.suc b , a'≢b') =
  Fin.suc (del {x} a (b , λ a≡b → ⊥-elim (a'≢b' (≡.cong Fin.suc a≡b))))

del-zero-suc : ∀ {x} (b : Fin x) (a≢b : Fin.zero ≢ Fin.suc b) → del Fin.zero (Fin.suc b , a≢b) ≡ b
del-zero-suc b a≢b with del Fin.zero (Fin.suc b , a≢b) | inspect (del Fin.zero) (Fin.suc b , a≢b)
... | Fin.zero | [ eq ] = ≡.sym eq
... | Fin.suc X | [ eq ] = ≡.sym eq

del-inj : {x : ℕ} → (a : Fin (ℕ.suc x))
        → (B₁ : Σ[ b₁ ∈ Fin (ℕ.suc x) ] a ≢ b₁)
        → (B₂ : Σ[ b₂ ∈ Fin (ℕ.suc x) ] a ≢ b₂)
        → del a B₁ ≡ del a B₂
        → proj₁ B₁ ≡ proj₁ B₂
del-inj Fin.zero (Fin.zero , a≢b₁) (Fin.zero , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj Fin.zero (Fin.zero , a≢b₁) (Fin.suc b₂ , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj Fin.zero (Fin.suc b₁ , a≢b₁) (Fin.zero , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₂ ≡.refl)
del-inj Fin.zero (Fin.suc b₁ , a≢b₁) (Fin.suc b₂ , a≢b₂) b₁'≡b₂' =
  let b₁' = del Fin.zero (Fin.suc b₁ , a≢b₁)
      b₂' = del Fin.zero (Fin.suc b₂ , a≢b₂)
      b₁'≡b₁ : b₁' ≡ b₁
      b₁'≡b₁ = del-zero-suc b₁ a≢b₁
      b₂'≡b₂ : b₂' ≡ b₂
      b₂'≡b₂ = del-zero-suc b₂ a≢b₂
  in begin
      Fin.suc b₁
    ≡⟨ ≡.cong Fin.suc (≡.sym b₁'≡b₁) ⟩
      Fin.suc b₁'
    ≡⟨ ≡.cong Fin.suc b₁'≡b₂' ⟩
      Fin.suc b₂'
    ≡⟨ ≡.cong Fin.suc b₂'≡b₂ ⟩
      Fin.suc b₂ ∎
del-inj (Fin.suc a) (Fin.zero , a≢b₁) (Fin.zero , a≢b₂) b₁'≡b₂' = ≡.refl
del-inj (Fin.suc a) (Fin.zero , a≢b₁) (Fin.suc b₂ , a≢b₂) b₁'≡b₂'
  with del (Fin.suc a) (Fin.zero , a≢b₁) | inspect (del (Fin.suc a)) (Fin.zero , a≢b₁) | del (Fin.suc a) (Fin.suc , a≢b₂) | inspect (del (Fin.suc a)) (Fin.suc b₂ , a≢b₂)
... | Fin.zero | [ eq ] | A | B = {!!}
... | Fin.suc X | Y | A | B = {!!}
  -- let b₁' = del (Fin.suc a) (Fin.zero , a≢b₁)
  --     b₂' = del (Fin.suc a) (Fin.suc b₂ , a≢b₂)
  --     b₂'≡b₂ : b₂' ≡ b₂
  --     b₂'≡b₂ = del-zero-suc b₂ a≢b₂
  -- in begin
  --     ?
  --   ≡⟨ ? ⟩
  --     ? ∎
del-inj (Fin.suc a) (Fin.suc b₁ , a≢b₁) (Fin.zero , a≢b₂) b₁'≡b₂' = {!!}
del-inj (Fin.suc a) (Fin.suc b₁ , a≢b₁) (Fin.suc b₂ , a≢b₂) b₁'≡b₂' = {!!}

module _ {x y : ℕ} (f : Fin (ℕ.suc x) → Fin (ℕ.suc y)) (inj : injective f) where
  sub : Σ[ f' ∈ (Fin x → Fin y) ] injective f'
  sub =
    let f' : Fin x → Fin y
        f' i =
          let (j , 0≢j) = add Fin.zero i 
              k = f j
              l = del (f Fin.zero) (k , λ f0≡fj → 0≢j (inj Fin.zero j f0≡fj))
          in l
    in f' , (λ a b f'a≡f'b →
      let (a₁ , 0≢a₁) = add Fin.zero a
          (b₁ , 0≢b₁) = add Fin.zero b 
          a₂ = f a₁
          b₂ = f b₁
          a₃ = del (f Fin.zero) (a₂ , (λ f0≡fa₁ → 0≢a₁ (inj Fin.zero a₁ f0≡fa₁)))
          b₃ = del (f Fin.zero) (b₂ , (λ f0≡fb₁ → 0≢b₁ (inj Fin.zero b₁ f0≡fb₁)))
          X = inj a₁ b₁ {!!}
      in {!!})

--with (i ≟ Fin.zero)
--... | yes i≡0 = {!!}
--... | no i≢0 = {!!}

_-A : {x y a : ℕ} → (f : Fin (a + x) → Fin (a + y)) → {inj : injective f}
    → Σ[ f' ∈ (Fin x → Fin y) ] injective f'
_-A {a = ℕ.zero} f {inj} = f , inj
_-A {a = ℕ.suc a} f = {!!}

