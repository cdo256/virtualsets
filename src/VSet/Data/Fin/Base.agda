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

fzero≢fsuc : ∀ {x : ℕ} (i : Fin x) → fzero ≢ fsuc i
fzero≢fsuc {x} i p = transport (cong P p) tt
  where
    P : {x : ℕ} → Fin (suc x) → Type
    P {x} fzero = ⊤ 
    P {x} (fsuc a) = ⊥

fsuc≢fzero : ∀ {x : ℕ} (i : Fin x) → fsuc i ≢ fzero 
fsuc≢fzero a = ≢sym (fzero≢fsuc a) 

toℕ : ∀ {n} → Fin n → ℕ 
toℕ fzero = zero
toℕ (fsuc x) = suc (toℕ x)

fromℕ : ∀ {n} → (a : ℕ) → (a < n) → Fin n
fromℕ {zero} a a<0 = absurd (¬-<-zero {a} a<0)
fromℕ {suc n} zero _ = fzero
fromℕ {suc n} (suc a) sa<sn = fsuc (fromℕ {n} a (pred-<-pred {a} {n} sa<sn))

toℕ∘fromℕ≡id : {m : ℕ} → (n : ℕ) → (n<m : n < m) → toℕ {m} (fromℕ n n<m) ≡ n
toℕ∘fromℕ≡id {zero} n n<0 = absurd (¬-<-zero n<0)
toℕ∘fromℕ≡id {suc m} zero 0<sm = refl
toℕ∘fromℕ≡id {suc m} (suc n) sn<sm = cong suc (toℕ∘fromℕ≡id n (pred-<-pred sn<sm))

toℕ<m : ∀ {m : ℕ} → (a : Fin m) → toℕ a < m 
toℕ<m {suc m} fzero = suc-<-suc tt
toℕ<m {suc m} (fsuc a) = suc-<-suc (toℕ<m a)

fromℕ∘toℕ≡id : {m : ℕ} → (a : Fin m) → fromℕ (toℕ {m} a) (toℕ<m a) ≡ a
fromℕ∘toℕ≡id {suc m} fzero = refl
fromℕ∘toℕ≡id {suc m} (fsuc a) =
  fromℕ (toℕ (fsuc a)) (toℕ<m (fsuc a))
    ≡⟨ refl ⟩
  fromℕ (suc (toℕ a)) (suc-<-suc a<m)
    ≡⟨ refl ⟩
  fsuc (fromℕ (toℕ a) (pred-<-pred (suc-<-suc a<m)))
    ≡⟨ cong (λ ○ → fsuc (fromℕ (toℕ a) ○)) refl ⟩
  fsuc (fromℕ (toℕ a) a<m)
    ≡⟨ cong fsuc (fromℕ∘toℕ≡id a) ⟩
  fsuc a ∎
  where
    a<m = toℕ<m a

pred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
pred fzero = fzero
pred (fsuc n) = n

fsuc-injective : ∀ {n} {i j : Fin n} → fsuc {n} i ≡ fsuc {n} j → i ≡ j
fsuc-injective {zero} {()} {()} 
fsuc-injective {suc n} {i} {j} p = cong pred p

fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x +ℕ y)
fshift zero a = a
fshift (suc x) a = fsuc (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x +ℕ y)
finject {x} zero a = subst Fin (sym (ℕ.+-zero x)) a
finject {suc x} (suc y) fzero = fzero
finject {suc x} (suc y) (fsuc a) = fsuc (finject {x} (suc y) a)

