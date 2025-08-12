# The trouble with representing Fin in Cubical Agda

In type theory, a `Fin` is a type family that represents 

```
module Notes.FinProblems where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives

open import Cubical.Data.Empty renaming (elim to absurd)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit.Base renaming (Unit to ⊤)

_≢_ : ∀ {ℓ} {A : Type ℓ} → (x y : A) → Type ℓ
x ≢ y = x ≡ y → ⊥

≢sym : {A : Type} {x y : A} → (x ≢ y) → (y ≢ x)
≢sym x≢y y≡x = x≢y (sym y≡x)

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

fzero≢fsuc : ∀ {x : ℕ} {i : Fin x} → fzero ≢ fsuc i
fzero≢fsuc {x} {i} p = transport (cong P p) tt
  where
    P : {x : ℕ} → Fin (suc x) → Type
    P {x} fzero = ⊤ 
    P {x} (fsuc a) = ⊥

fsuc≢fzero : ∀ {n} {i : Fin n} → fsuc i ≢ fzero 
fsuc≢fzero {i = i} = ≢sym (fzero≢fsuc {i = i}) 

toℕ : ∀ {n} → Fin n → ℕ 
toℕ fzero = zero
toℕ (fsuc x) = suc (toℕ x)

fromℕ : ∀ {n} → (a : ℕ) → (a < n) → Fin n
fromℕ {zero} a sa≤0 = absurd (¬-<-zero sa≤0)
fromℕ {suc n} zero (x , x+a≡n) = fzero
fromℕ {suc n} (suc a) sa<sn = fsuc (fromℕ {n} a (pred-≤-pred sa<sn))

toℕ∘fromℕ≡id : {m : ℕ} → (n : ℕ) → (n<m : n < m) → toℕ (fromℕ n n<m) ≡ n
toℕ∘fromℕ≡id {zero} n n<0 = absurd (¬-<-zero n<0)
toℕ∘fromℕ≡id {suc m} zero 0<sm = refl
toℕ∘fromℕ≡id {suc m} (suc n) sn<sm = cong suc (toℕ∘fromℕ≡id n (pred-≤-pred sn<sm))

toℕ<m : ∀ {m} → (a : Fin m) → toℕ a < m 
toℕ<m {suc m} fzero = suc-≤-suc zero-≤
toℕ<m {suc m} (fsuc a) = suc-≤-suc (toℕ<m a)

-- Not possible?
fromℕ∘toℕ≡id : {m : ℕ} → (a : Fin m) → fromℕ (toℕ {m} a) (toℕ<m a) ≡ a
fromℕ∘toℕ≡id {suc m} fzero = refl
fromℕ∘toℕ≡id {suc m} (fsuc a) =
  fromℕ (toℕ (fsuc a)) (toℕ<m (fsuc a)) ≡⟨ refl ⟩
  fromℕ (suc (toℕ a)) (suc-≤-suc (toℕ<m a)) ≡⟨ {!refl!} ⟩
  fsuc (fromℕ (toℕ a) (toℕ<m a)) ≡⟨ cong fsuc (fromℕ∘toℕ≡id a) ⟩
  fsuc a ∎ 

fsuc-injective : ∀ {n} {i j : Fin n} → fsuc i ≡ fsuc j → i ≡ j
fsuc-injective {suc n} {fzero} {fzero} p = refl
fsuc-injective {suc n} {fzero} {fsuc j} p = absurd (fzero≢fsuc {!!})
fsuc-injective {suc n} {fsuc i} {j} p = {!!}
```
