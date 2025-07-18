module VSet.Data.Fin.Base where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order

open ℕ.ℕ

private
  variable
    ℓ : Level

data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

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
fromℕ {zero} a a<0 = absurd (¬-<-zero {a} a<0)
fromℕ {suc n} zero _ = fzero
fromℕ {suc n} (suc a) sa<sn = fsuc (fromℕ {n} a (pred-<-pred {a} {n} sa<sn))

pred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
pred fzero = fzero
pred (fsuc n) = n

fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x +ℕ y)
fshift zero a = a
fshift (suc x) a = fsuc (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x +ℕ y)
finject {suc x} zero fzero = fzero
finject {suc x} zero (fsuc a) = fsuc (finject zero a)
finject {suc x} (suc y) fzero = fzero
finject {suc x} (suc y) (fsuc a) = fsuc (finject {x} (suc y) a)

finject-subst-commute
  : ∀ {x y z : ℕ} → (p : x ≡ z) → (a : Fin x)
  → finject {z} y (subst Fin p a) ≡ subst (λ ○ → Fin (○ +ℕ y)) p (finject {x} y a)
finject-subst-commute {x} {y} {z} p a =
  substRefl {B = (λ ○ → Fin (○ +ℕ y))} ? ?

-- finject-subst-commute {suc x} {zero} {zero} p fzero =
--   {!refl!}
-- finject-subst-commute {suc x} {zero} {zero} p (fsuc a) = {!!}
-- finject-subst-commute {suc x} {zero} {suc z} p a = {!!}
-- finject-subst-commute {suc x} {suc y} {z} p a = {!!}
