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

⟦_⟧ : ℕ → Type
⟦_⟧ = Fin

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
fromℕ {zero} a a<0 = absurd {A = Fin 0} (¬-<-zero {a} a<0)
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
finject {suc x} y (fsuc a) = fsuc (finject {x} y a)

finj : {x : ℕ} → (a : Fin x) → Fin (suc x)
finj fzero = fzero
finj (fsuc a) = fsuc (finj a)

fmax : ∀ {x} → Fin (suc x)
fmax {zero} = fzero
fmax {suc x} = fsuc (fmax {x})

fzero≢fsuc : ∀ {x : ℕ} (i : Fin x) → fzero ≢ fsuc i
fzero≢fsuc {x} i p = transport (cong P p) tt
  where
    P : {x : ℕ} → Fin (suc x) → Type
    P {x} fzero = ⊤
    P {x} (fsuc a) = ⊥

fsuc≢fzero : ∀ {x : ℕ} (i : Fin x) → fsuc i ≢ fzero 
fsuc≢fzero a = ≢sym (fzero≢fsuc a) 

Fin0≃⊥ : Fin 0 ≃ ⊥
Fin0≃⊥ = (λ ()) , record { equiv-proof = λ y → absurd y }

Fin0-absurd : {A : Type ℓ} → Fin 0 → A
Fin0-absurd ()

fsuc-injective : ∀ {n} {i j : Fin n} → fsuc {n} i ≡ fsuc {n} j → i ≡ j
fsuc-injective {zero} {()} {()} 
fsuc-injective {suc n} {i} {j} p = cong pred p
