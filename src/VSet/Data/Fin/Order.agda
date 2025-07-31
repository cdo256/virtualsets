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
    x y : ℕ

data _<ᶠ_ : {x : ℕ} (a b : Fin x) → Type where
 <fzero : ∀ {x} {b : Fin x} → fzero <ᶠ fsuc b
 <fsuc : ∀ {x} {a b : Fin x} →  a <ᶠ b → fsuc a <ᶠ fsuc b

_≤ᶠ_ : ∀ {x} (a b : Fin x) → Type
a ≤ᶠ b = (a <ᶠ b) ⊎ (a ≡ b)

data Trichotomyᶠ {x} (a b : Fin x) : Type where
  flt : a <ᶠ b → Trichotomyᶠ a b
  feq : a ≡ b → Trichotomyᶠ a b
  fgt : b <ᶠ a → Trichotomyᶠ a b

open Trichotomyᶠ

data Bichotomyᶠ {x} (a b : Fin x) : Type where
  fle : a ≤ᶠ b → Bichotomyᶠ a b
  fgt : b <ᶠ a → Bichotomyᶠ a b

open Bichotomyᶠ

_≟ᶠ-suc_ : ∀ {x} → (a b : Fin x)
          → Trichotomyᶠ a b → Trichotomyᶠ (fsuc a) (fsuc b) 
(a ≟ᶠ-suc b) (flt a<b) = flt (<fsuc a<b)
(a ≟ᶠ-suc b) (feq a≡b) = feq (cong fsuc a≡b)
(a ≟ᶠ-suc b) (fgt b<a) = fgt (<fsuc b<a)

_≟ᶠ_ : ∀ {x} → (a b : Fin x) → Trichotomyᶠ a b 
fzero ≟ᶠ fzero = feq refl
fzero ≟ᶠ fsuc b = flt <fzero
fsuc a ≟ᶠ fzero = fgt <fzero
fsuc a ≟ᶠ fsuc b = (a ≟ᶠ-suc b) (a ≟ᶠ b)

Trichotomy→Bichotomyᶠ
  : ∀ {x} {a b : Fin x}
  → Trichotomyᶠ a b → Bichotomyᶠ a b 
Trichotomy→Bichotomyᶠ (flt a<b) = fle (inl a<b)
Trichotomy→Bichotomyᶠ (feq a≡b) = fle (inr a≡b)
Trichotomy→Bichotomyᶠ (fgt b<a) = fgt b<a

_≤?ᶠ_ : ∀ {x} → (a b : Fin x) → Bichotomyᶠ a b 
a ≤?ᶠ b = Trichotomy→Bichotomyᶠ (a ≟ᶠ b)

¬a<a : ∀ {x} → (a : Fin x) → ¬ a <ᶠ a
¬a<a (fsuc a) (<fsuc a<a) = ¬a<a a a<a

<ᶠ→≢ : ∀ {x} → {a b : Fin x} → a <ᶠ b → a ≢ b
<ᶠ→≢ {a = fzero} {b = fsuc b} <fzero a≡b = fzero≢fsuc b a≡b
<ᶠ→≢ {a = fsuc a} {b = fsuc b} (<fsuc a<b) a≡b =
  <ᶠ→≢ {a = a} {b = b} a<b (fsuc-injective a≡b)

<ᶠ-respects-pred : ∀ {x} → {a b : Fin x} → fsuc a <ᶠ fsuc b → a <ᶠ b
<ᶠ-respects-pred (<fsuc a'<b') = a'<b'

≤ᶠ-respects-pred : ∀ {x} → {a b : Fin x} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤ᶠ-respects-pred (inl a'<b') = inl (<ᶠ-respects-pred a'<b')
≤ᶠ-respects-pred (inr a'≡b') = inr (fsuc-injective a'≡b')

≤ᶠ-respects-fsuc : ∀ {x} → {a b : Fin x} → a ≤ᶠ b → fsuc a ≤ᶠ fsuc b 
≤ᶠ-respects-fsuc (inl a<b) = inl (<fsuc a<b)
≤ᶠ-respects-fsuc (inr a≡b) = inr (cong fsuc a≡b)

fzero≤a : ∀ {x : ℕ} → (a : Fin (suc x)) → fzero ≤ᶠ a
fzero≤a fzero = inr refl
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

case≤?ᶠ : {A : Type} {m : ℕ} (a b : Fin m) → A → A → A
case≤?ᶠ a b x y = case (a ≤?ᶠ b) of
  λ{ (fle _) → x
   ; (fgt _) → y }
