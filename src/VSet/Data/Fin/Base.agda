module VSet.Data.Fin.Base where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order

open ℕ.ℕ

private
  variable
    ℓ : Level
    x y : ℕ

data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

f0 : Fin (1 ℕ.+ x)
f0 = fzero
f1 : Fin (2 ℕ.+ x)
f1 = fsuc f0
f2 : Fin (3 ℕ.+ x)
f2 = fsuc f1
f3 : Fin (4 ℕ.+ x)
f3 = fsuc f2
f4 : Fin (5 ℕ.+ x)
f4 = fsuc f3
f5 : Fin (6 ℕ.+ x)
f5 = fsuc f4
f6 : Fin (7 ℕ.+ x)
f6 = fsuc f5
f7 : Fin (8 ℕ.+ x)
f7 = fsuc f6
f8 : Fin (9 ℕ.+ x)
f8 = fsuc f7
f9 : Fin (10 ℕ.+ x)
f9 = fsuc f8

{-# DISPLAY fzero = f0 #-}
{-# DISPLAY fsuc fzero = f1 #-}
{-# DISPLAY fsuc (fsuc fzero) = f2 #-}
{-# DISPLAY fsuc (fsuc (fsuc fzero)) = f3 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc fzero))) = f4 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc fzero)))) = f5 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = f6 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = f7 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = f8 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = f9 #-}

elim : ∀ {A : {n : ℕ} → Fin (suc n) → Type }
     → ({n : ℕ} → A {n} fzero)
     → ({n : ℕ} → (a : Fin (suc n)) → A a → A (fsuc a))
     → ((m : ℕ) → (a : Fin (suc m)) → A a)
elim {A = A} z s m fzero = z
elim {A = A} z s (suc m) (fsuc a) = s a (elim {A = A} z s m a)

toℕ : ∀ {n} → Fin n → ℕ 
toℕ fzero = zero
toℕ (fsuc x) = suc (toℕ x)

fromℕ : ∀ {n} → (a : ℕ) → (a < n) → Fin n
fromℕ {zero} a a<0 = absurd {A = λ _ → Fin 0} (¬-<-zero {a} a<0)
fromℕ {suc n} zero _ = fzero
fromℕ {suc n} (suc a) sa<sn = fsuc (fromℕ {n} a (pred-<-pred {a} {n} sa<sn))

pred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
pred fzero = fzero
pred (fsuc n) = n

fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x +ℕ y)
fshift zero a = a
fshift (suc x) a = fsuc (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x +ℕ y)
finject {suc _} _ fzero = fzero
finject {suc _} zero (fsuc a) = fsuc (finject zero a)
finject {suc x} (suc y) (fsuc a) = fsuc (finject {x} (suc y) a)

fmax : ∀ {x} → Fin (suc x)
fmax {zero} = fzero
fmax {suc x} = fsuc (fmax {x})

data _<ᶠ_ : {x : ℕ} (a b : Fin x) → Type where
 <fzero : ∀ {x} {b : Fin x} → fzero <ᶠ fsuc b
 <fsuc : ∀ {x} {a b : Fin x} →  a <ᶠ b → fsuc a <ᶠ fsuc b

data Trichotomyᶠ {x} (a b : Fin x) : Type where
  flt : a <ᶠ b → Trichotomyᶠ a b
  feq : a ≡ b → Trichotomyᶠ a b
  fgt : b <ᶠ a → Trichotomyᶠ a b

open Trichotomyᶠ

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
