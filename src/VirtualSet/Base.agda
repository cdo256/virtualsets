module VirtualSet.Base where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Fin
  using (Fin)
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


private
  variable
    c ℓ : Level.Level

injective : {X Y : Set} → (f : X → Y) → Set
injective {X} {Y} f = ∀ (a b : X) → f a ≡ f b → a ≡ b

injective : {X Y : Set} → (f : X → Y) → Set
injective {X} {Y} f = ∀ (a b : X) → f a ≡ f b → a ≡ b

add : {x : ℕ} → (a : Fin (ℕ.suc x)) → (b : Fin x) → (Σ[ c ∈ Fin (ℕ.suc x) ] a ≢ c)
add {ℕ.suc x} Fin.zero b = Fin.suc b , λ ()
add {ℕ.suc x} (Fin.suc a) Fin.zero = Fin.zero , λ ()
add {ℕ.suc x} (Fin.suc a) (Fin.suc b) =
  let
    (c , a≢c) = add a b
  in Fin.suc (proj₁ (add a b)) , λ a'≡c' → a≢c {!!}

del : {x : ℕ} → (a : Fin (ℕ.suc x)) → (Σ[ b ∈ Fin (ℕ.suc x) ] a ≢ b) → Fin x
del {ℕ.zero} Fin.zero (Fin.zero , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} Fin.zero (Fin.zero , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} Fin.zero (Fin.suc b , a≢b) = b
del {ℕ.suc x} (Fin.suc a) (Fin.zero , a≢b) = Fin.zero
del {ℕ.suc x} (Fin.suc a) (Fin.suc b , a'≢b') =
  Fin.suc (del {x} a (b , λ a≡b → ⊥-elim (a'≢b' (≡.cong Fin.suc a≡b))))

sub : {x y : ℕ} → (f : Fin (ℕ.suc x) → Fin (ℕ.suc y)) → (inj : injective f)
    → (Fin x → Fin y)
sub {x} {y} f inj i = {!!}
  where j : ℕ
        j = x 

_-A : {x y a : ℕ} → (f : Fin (a + x) → Fin (a + y)) → {inj : injective f}
    → Σ[ f' ∈ (Fin x → Fin y) ] injective f'
_-A {a = ℕ.zero} f {inj} = f , inj
_-A {a = ℕ.suc a} f = {!!}

