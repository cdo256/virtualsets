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

fsplice : ∀ {x} → Fin (suc x) → Fin x → Fin (suc x)
fsplice fzero a = fsuc a
fsplice (fsuc b) fzero = fzero
fsplice (fsuc b) (fsuc a) = fsuc (fsplice b a)

-- Alternate definition.
fsplice' : ∀ {x : ℕ} → Fin (suc x) → Fin x → Fin (suc x)
fsplice' b a with b ≤?ᶠ finj a
... | fle b≤a = fsuc a
... | fgt a<b = finj a

-- Inverse to finj whenever a is not max.
funinj : Fin (suc (suc x)) → Fin (suc x)
funinj {x = zero} a = fzero
funinj {x = suc x} fzero = fzero
funinj {x = suc zero} (fsuc a) = fzero
funinj {x = suc (suc x)} (fsuc a) = fsuc (funinj a)

-- Remove a from domain of b
funsplice : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x))) → .(a ≢ b)
          → Fin (suc x)
funsplice {x = zero} _ _ _ = fzero
funsplice {x = suc x} _ fzero _ = fzero
funsplice {x = suc x} fzero (fsuc a) _ = a
funsplice {x = suc x} (fsuc b) (fsuc a) a'≢b' =
  fsuc (funsplice b a λ a≡b → a'≢b' (cong fsuc a≡b))

-- Alternate definition
funsplice' : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x))) → a ≢ b
          → Fin (suc x)
funsplice' b a a≢b with a ≟ᶠ b
... | flt a<b = funinj a
... | feq a≡b = absurd (a≢b a≡b)
... | fgt b<a = pred a
