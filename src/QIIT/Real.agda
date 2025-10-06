module QIIT.Real where

open import VSet.Prelude hiding (lower)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order using () renaming (_≤_ to _≤ᴺ_)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Int as ℤ
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.NatPlusOne as ℕ₊₁
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; _·₊₁_)
import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals using (ℚ; [_/_])
open import Cubical.Data.Rationals.Order
  using () renaming (_≤_ to _≤ꟴ_; _<_ to _<ꟴ_; ≤Dec to ≤Decꟴ)
import Cubical.Data.Bool as 𝔹
open import Cubical.Data.Bool
  using (true; false; if_then_else_) renaming (Bool to 𝔹)

private
  variable
    ℓ ℓ' ℓ'' : Level

isSurjective : {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → Type _
isSurjective {A = A} {B} f = (b : B) → Σ[ a ∈ A ] f a ≡ b

isMonotonicℚ→Type : (f : ℚ → Type ℓ) → Type _
isMonotonicℚ→Type f = ∀ x y → x ≤ꟴ y → f x → f y

isMonotonicℕ→ℚ : (f : ℕ → ℚ) → Type _
isMonotonicℕ→ℚ f = ∀ (x y : ℕ) → x ≤ᴺ y → f x ≤ꟴ f y

isBounded : (f : ℚ → Type ℓ) → Type _
isBounded f = (Σ[ x ∈ ℚ ] ¬ f x) × (Σ[ x ∈ ℚ ] f x)

record ℝ : Type (ℓ-suc ℓ) where
  field
    Fun : ℚ → Type ℓ
    dec : (x : ℚ) → Dec (Fun x)
    bounded : isBounded Fun
    monotonic : isMonotonicℚ→Type Fun

open ℝ

sign : ℕ → ℤ
sign n = if ℕ.isEven n then ℤ.pos 1 else ℤ.negsuc 0

ℕ→ℕ₊₁ : (n : ℕ) → n ≢ 0 → ℕ₊₁
ℕ→ℕ₊₁ ℕ.zero 0≢0 = absurd (0≢0 refl) 
ℕ→ℕ₊₁ (ℕ.suc n) _ = 1+ n
ℕ→ℤ : ℕ → ℤ
ℕ→ℤ = ℤ.pos
ℤ→ℚ : ℤ → ℚ
ℤ→ℚ x = [ x / 1+ 0 ]
ℕ→ℚ : ℕ → ℚ
ℕ→ℚ = ℤ→ℚ ∘ ℕ→ℤ

ℚSeries : ((n : ℕ) → ℚ) → (m : ℕ) → ℚ
ℚSeries f ℕ.zero = ℕ→ℚ 0
ℚSeries f (ℕ.suc m) = f m ℚ.+ ℚSeries f m

πGregoryLeibnizTerm : (n : ℕ) → ℚ
πGregoryLeibnizTerm n = [ sign n / 1+ (2 ℕ.· n) ]

πGregoryLeibniz = ℚSeries πGregoryLeibnizTerm 

module NilakanthaPi where

  term : ℕ → ℚ
  term ℕ.zero = ℕ→ℚ 3
  term (ℕ.suc n) = [ num / denom ]
    where
      num : ℤ
      num = ℕ→ℤ 4 ℤ.· sign n
      denom : ℕ₊₁
      denom = (1+ (2 ℕ.· n ℕ.+ 1) ·₊₁ 1+ (2 ℕ.· n ℕ.+ 2) ·₊₁ 1+ (2 ℕ.· n ℕ.+ 3))

  series = ℚSeries term
  upper : ℕ → ℚ
  upper n = series (2 ℕ.· n ℕ.+ 1)
  lower : ℕ → ℚ
  lower n = series (2 ℕ.· n)

  upperIsMonatonicℚ : {!!}

  Covering : (x : ℚ) → (Σ[ n ∈ ℕ ] x ≤ꟴ lower n) ⊎ (Σ[ n ∈ ℕ ] upper n ≤ꟴ x)
  Covering x = {!!}

  MutuallyExclusive
    : (x : ℚ)
    → (Σ[ n ∈ ℕ ] x ≤ꟴ lower n)
    → (Σ[ n ∈ ℕ ] upper n ≤ꟴ x)
    → ⊥
  MutuallyExclusive x (n1 , x≤lower) (n2 , x≥upper) = {!!}

  F : ℚ → Type _
  F x = Σ[ n ∈ ℕ ] upper n ≤ꟴ x

  π : ℝ
  π .Fun = F
  π .dec x = {!!}
  π .bounded = (ℕ→ℚ 0 , ¬F0) , (ℕ→ℚ 4 , F4)
    where
      ¬F0 : ¬ F (ℕ→ℚ 0)
      ¬F0 (n , 0≤n) = {!!}
      F4 : F (ℕ→ℚ 4)
      F4 = 0 , ({!!} , {!!})
  π .monotonic = {!!}
