module VSet.Data.Fin.Order where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order
open import VSet.Data.Fin.Base

open ℕ.ℕ

private
  variable
    ℓ : Level
    x y z : ℕ
    a : Fin x
    b : Fin y
    c : Fin z

data _<ᶠ_ : {x y : ℕ} (a : Fin x) → (b : Fin y) → Type where
  <fzero : {b : Fin y} → (fzero {x}) <ᶠ fsuc b
  <fsuc : {a : Fin x} {b : Fin y} → a <ᶠ b → fsuc a <ᶠ fsuc b

data _≈ᶠ_ : {x y : ℕ} (a : Fin x) → (b : Fin y) → Type where
  ≈fzero : (fzero {x}) ≈ᶠ (fzero {y})
  ≈fsuc : {a : Fin x} {b : Fin y} → a ≈ᶠ b → fsuc a ≈ᶠ fsuc b

≈fsym : a ≈ᶠ b → b ≈ᶠ a
≈fsym ≈fzero = ≈fzero
≈fsym (≈fsuc a≈b) = ≈fsuc (≈fsym a≈b)

≈refl : a ≈ᶠ a
≈refl {a = fzero} = ≈fzero
≈refl {a = fsuc a} = ≈fsuc (≈refl {a = a})

≡→≈ᶠ : {a b : Fin x} → a ≡ b → a ≈ᶠ b 
≡→≈ᶠ {a = a} a≡b = subst (a ≈ᶠ_) a≡b ≈refl

≈ᶠ→≡ : {a b : Fin x} → a ≈ᶠ b → a ≡ b
≈ᶠ→≡ ≈fzero = refl
≈ᶠ→≡ (≈fsuc a≈b) = cong fsuc (≈ᶠ→≡ a≈b)

_≉ᶠ_ : Fin x → Fin y → Type
a ≉ᶠ b = ¬ a ≈ᶠ b

fzero≉fsuc : fzero {x} ≉ᶠ fsuc b
fzero≉fsuc ()

fsuc≉fzero : fsuc a ≉ᶠ fzero {y}
fsuc≉fzero ()

≈fsuc-injective : fsuc a ≈ᶠ fsuc b → a ≈ᶠ b
≈fsuc-injective (≈fsuc a≈b) = a≈b

_≤ᶠ_ : (a : Fin x) (b : Fin y) → Type
_≤ᶠ_ {x = x} {y = y} a b = (a <ᶠ b) ⊎ (a ≈ᶠ b)

isProp<ᶠ : {a b : Fin x} → isProp (a <ᶠ b)
isProp<ᶠ <fzero <fzero = refl
isProp<ᶠ (<fsuc x) (<fsuc y) = cong <fsuc (isProp<ᶠ x y)

data Trichotomyᶠ {x y} (a : Fin x) (b : Fin y) : Type where
  flt : a <ᶠ b → Trichotomyᶠ a b
  feq : a ≈ᶠ b → Trichotomyᶠ a b
  fgt : b <ᶠ a → Trichotomyᶠ a b

open Trichotomyᶠ

data Bichotomyᶠ {x y} (a : Fin x) (b : Fin y) : Type where
  fle : a ≤ᶠ b → Bichotomyᶠ a b
  fgt : b <ᶠ a → Bichotomyᶠ a b

open Bichotomyᶠ

_≟ᶠ-suc_ : ∀ {x} → (a : Fin x) (b : Fin y)
          → Trichotomyᶠ a b → Trichotomyᶠ (fsuc a) (fsuc b) 
(a ≟ᶠ-suc b) (flt a<b) = flt (<fsuc a<b)
(a ≟ᶠ-suc b) (feq a≈b) = feq (≈fsuc a≈b)
(a ≟ᶠ-suc b) (fgt b<a) = fgt (<fsuc b<a)

_≟ᶠ_ : ∀ (a : Fin x) (b : Fin y) → Trichotomyᶠ a b 
fzero ≟ᶠ fzero = feq (≈fzero)
fzero ≟ᶠ fsuc b = flt <fzero
fsuc a ≟ᶠ fzero = fgt <fzero
fsuc a ≟ᶠ fsuc b = (a ≟ᶠ-suc b) (a ≟ᶠ b)

Trichotomy→Bichotomyᶠ
  : ∀ {x} {a : Fin x} {b : Fin y}
  → Trichotomyᶠ a b → Bichotomyᶠ a b 
Trichotomy→Bichotomyᶠ (flt a<b) = fle (inl a<b)
Trichotomy→Bichotomyᶠ (feq a≈b) = fle (inr a≈b)
Trichotomy→Bichotomyᶠ (fgt b<a) = fgt b<a

_≤?ᶠ_ : (a : Fin x) (b : Fin y) → Bichotomyᶠ a b 
a ≤?ᶠ b = Trichotomy→Bichotomyᶠ (a ≟ᶠ b)

¬a<a : (a : Fin x) → ¬ a <ᶠ a
¬a<a (fsuc a) (<fsuc a<a) = ¬a<a a a<a

<ᶠ→≉ : {a : Fin x} {b : Fin y} → a <ᶠ b → a ≉ᶠ b
<ᶠ→≉ {a = fzero} {b = fsuc b} <fzero a≈b = fzero≉fsuc a≈b
<ᶠ→≉ {a = fsuc a} {b = fsuc b} (<fsuc a<b) a≈b =
  <ᶠ→≉ {a = a} {b = b} a<b (≈fsuc-injective a≈b)

≤ᶠ→≯ᶠ : {a : Fin x} {b : Fin y} → a ≤ᶠ b → ¬ b <ᶠ a
≤ᶠ→≯ᶠ (inl (<fsuc a<b)) (<fsuc a>b) = ≤ᶠ→≯ᶠ (inl a<b) a>b
≤ᶠ→≯ᶠ (inr a≈b) a>b = <ᶠ→≉ a>b (≈fsym a≈b)

<ᶠ-respects-pred : {a : Fin x} {b : Fin y} → fsuc a <ᶠ fsuc b → a <ᶠ b
<ᶠ-respects-pred (<fsuc a'<b') = a'<b'

≤ᶠ-respects-pred : {a : Fin x} {b : Fin y} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤ᶠ-respects-pred (inl a'<b') = inl (<ᶠ-respects-pred a'<b')
≤ᶠ-respects-pred (inr a'≈b') = inr (≈fsuc-injective a'≈b')

≤ᶠ-respects-fsuc : {a : Fin x} {b : Fin y} → a ≤ᶠ b → fsuc a ≤ᶠ fsuc b 
≤ᶠ-respects-fsuc (inl a<b) = inl (<fsuc a<b)
≤ᶠ-respects-fsuc (inr a≈b) = inr (≈fsuc a≈b)

fzero≤a : ∀ {x : ℕ} → (a : Fin (suc x)) → fzero {y} ≤ᶠ a
fzero≤a fzero = inr ≈fzero
fzero≤a (fsuc a) = inl <fzero

weaken<-pred : ∀ {x} {a : Fin (suc x)} {b : Fin x}
             → a <ᶠ fsuc b → a ≤ᶠ finj b 
weaken<-pred {a = a} {b = b} <fzero = fzero≤a (finj b)
weaken<-pred {a = fsuc a} {b = fsuc b} (<fsuc a<b) =
  ≤ᶠ-respects-fsuc (weaken<-pred a<b)

fin-restrict : ∀ {x} {b : Fin (suc x)} (a : Fin (suc x))
             → a <ᶠ b → Fin x
fin-restrict {suc x} fzero  <fzero = fzero
fin-restrict {suc x} (fsuc a) (<fsuc a<b) = fsuc (fin-restrict a a<b)

<ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a <ᶠ b → b <ᶠ c → a <ᶠ c
<ᶠ-trans <fzero (<fsuc b<c) = <fzero
<ᶠ-trans (<fsuc a<b) (<fsuc b<c) = <fsuc (<ᶠ-trans a<b b<c)

<-suc : ∀ (a : Fin x) → a <ᶠ fsuc a 
<-suc fzero = <fzero
<-suc (fsuc a) = <fsuc (<-suc a)

≤-pred : ∀ {a : Fin x} {b : Fin y} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤-pred (inl (<fsuc a<b)) = inl a<b
≤-pred (inr (≈fsuc a≈b)) = inr a≈b

fsuc≤fsuc : a ≤ᶠ b → fsuc a ≤ᶠ fsuc b
fsuc≤fsuc (inl a<b) = inl (<fsuc a<b)
fsuc≤fsuc (inr a≈b) = inr (≈fsuc a≈b)

≤ᶠ→<ᶠ : ∀ {x} {a : Fin x} {b : Fin x} → a ≤ᶠ b → a <ᶠ fsuc b
≤ᶠ→<ᶠ {b = b} (inl a<b) = <ᶠ-trans a<b (<-suc b) 
≤ᶠ→<ᶠ (inr ≈fzero) = <fzero
≤ᶠ→<ᶠ (inr (≈fsuc a≈b)) = <fsuc (≤ᶠ→<ᶠ (inr a≈b))

<ᶠ→≤ᶠ : ∀ {x} {a : Fin x} {b : Fin x} → a <ᶠ fsuc b → a ≤ᶠ b
<ᶠ→≤ᶠ {a = fzero} {fzero} a<b' = inr ≈fzero
<ᶠ→≤ᶠ {a = fzero} {fsuc b} 0<b' = inl <fzero
<ᶠ→≤ᶠ {a = fsuc a} {fsuc b} (<fsuc a<b) = fsuc≤fsuc (<ᶠ→≤ᶠ a<b)

fin-restrict-≤ : ∀ {x} {b : Fin x} (a : Fin (suc x))
               → a ≤ᶠ b → Fin x
fin-restrict-≤ a  = {!!}

fin-restrict' : ∀ {x} {b : Fin x} (a : Fin (suc x))
              → a ≤ᶠ b → Fin x
fin-restrict' {x = 0} {b} a x = b
fin-restrict' {x = suc x} {b = fsuc b} fzero (inl 0<b') = fzero
fin-restrict' {x = suc x} fzero (inr 0≈b) = fzero
fin-restrict' {x = suc x} {b = fsuc b} (fsuc a) (inl (<fsuc a<b)) = fsuc (fin-restrict' a (inl a<b))
fin-restrict' {x = suc x} {b = fzero} (fsuc a) (inr a'≈0) = absurd (fsuc≉fzero a'≈0)
fin-restrict' {x = suc x} {b = fsuc b} (fsuc a) (inr a'≈b') = fsuc (fin-restrict' a (inr (≈fsuc-injective a'≈b')))

case≤?ᶠ : {A : Type} {m : ℕ} (a b : Fin m) → A → A → A
case≤?ᶠ a b x y = case (a ≤?ᶠ b) of
  λ{ (fle _) → x
   ; (fgt _) → y }
