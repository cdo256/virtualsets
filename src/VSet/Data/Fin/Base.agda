module VSet.Data.Fin.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives

open import Cubical.Data.Empty renaming (elim to absurd)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order

open ℕ.ℕ

open import VSet.Path

private
  variable
    ℓ : Level

data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

fzero≢fsuc : ∀ i → fzero ≢ fsuc i
fzero≢fsuc ()

fsuc≢fzero : ∀ i → fsuc i ≢ fzero 
fsuc≢fzero a = ≢sym (fzero≢fsuc a) 



elim : ∀ {ℓ} {A : {n : ℕ} → Fin (suc n) → Type ℓ}
     → ({n : ℕ} → A {n} fzero)
     → ({n : ℕ} → (a : Fin (suc n)) → A a → A (fsuc a))
     → ((m : ℕ) → (a : Fin (suc m)) → A a)
elim {A = A} z s m fzero = z
elim {A = A} z s (suc m) (fsuc a) = s a (elim {A = A} z s m a)

suc-injective : ∀ {i j} → fsuc i ≡ fsuc j → i ≡ j
suc-injective {i} {j} p = elim {A = λ {n} x → {!!}} (λ {n} → {!!}) {!!} {!!} {!!}


fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x +ℕ y)
fshift zero a = a
fshift (suc x) a = fsuc (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x +ℕ y)
finject {x} zero a = subst Fin (sym (ℕ.+-zero x)) a
finject {suc x} (suc y) fzero = fzero
finject {suc x} (suc y) (fsuc a) = fsuc (finject {x} (suc y) a)

