module VSet.Data.Fin.Properties where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ; +-zero) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order

open import VSet.Data.Fin.Base
open import VSet.Function.Injection

open ℕ.ℕ

private
  variable
    ℓ : Level

fzero≢fsuc : ∀ {x : ℕ} (i : Fin x) → fzero ≢ fsuc i
fzero≢fsuc {x} i p = transport (cong P p) tt
  where
    P : {x : ℕ} → Fin (suc x) → Type
    P {x} fzero = ⊤
    P {x} (fsuc a) = ⊥

fsuc≢fzero : ∀ {x : ℕ} (i : Fin x) → fsuc i ≢ fzero 
fsuc≢fzero a = ≢sym (fzero≢fsuc a) 

Fin0≃⊥ : Fin 0 ≃ ⊥
Fin0≃⊥ = (λ ()) , record { equiv-proof = absurd }

Fin0-absurd : {A : Type ℓ} → Fin 0 → A
Fin0-absurd ()

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
  fsuc a ▯
  where
    a<m = toℕ<m a

fsuc-injective : ∀ {n} {i j : Fin n} → fsuc {n} i ≡ fsuc {n} j → i ≡ j
fsuc-injective {zero} {()} {()} 
fsuc-injective {suc n} {i} {j} p = cong pred p

-- finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x +ℕ y)
-- finject {suc x} zero fzero = fzero
-- finject {suc x} zero (fsuc a) = fsuc (finject zero a)
-- finject {suc x} (suc y) fzero = fzero
-- finject {suc x} (suc y) (fsuc a) = fsuc (finject {x} (suc y) a)

-- fzero-subst : {x y : ℕ} (p : suc x ≡ suc y) (a : Fin x)
--             → (λ i → {!!} i) [ fzero {n = y} ≡ subst Fin p (fzero {n = x}) ]
-- fzero-subst {x} {y} p a =
--   fzero {n = y} ≡P[ {!!} ][ p ∙P refl ]⟨ Fin ➢ {!!} ⟩ (subst Fin p (fzero {n = x}) ∎P)

finject0≡subst : {x : ℕ} (a : Fin x)
               → (λ i → Fin (+-zero x ( i))) [ finject {x} zero a ≡ a ]
finject0≡subst {suc x} fzero =
  finject zero fzero ≡P[ suc (x +ℕ 0) ][ cong suc {!(+-zero x)!} ∙P {!!} ]⟨ Fin ➢ {!!} ⟩
  (fzero {n = x} ∎P)

  -- finject zero fzero ≡⟨ refl ⟩
  -- fzero {n = x +ℕ 0} ≡⟨ cong (λ ○ → fzero {n = ○}) {!(+-zero x)!} ⟩
  -- {!fzero {n = x}!} ≡⟨ {!!} ⟩
  -- subst Fin (sym (+-zero (suc x))) fzero ▯
finject0≡subst {suc x} (fsuc a) = {!!}

finject-injective : {x : ℕ} → (y : ℕ) → is-injective (finject {x} y)
finject-injective {x} zero a b fa≡fb =
  a
    ≡⟨ sym (subst-inv Fin p a) ⟩
  subst Fin p (subst Fin (sym p) a)
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ {!!} ⟩
  {!!}
    ≡⟨ {!!} ⟩
  subst Fin p (subst Fin (sym p) b)
    ≡⟨ subst-inv Fin p b ⟩
  b ▯
  where
    p : x +ℕ 0 ≡ x
    p = ℕ.+-zero x 
finject-injective {x} (suc y) fzero fzero _ = refl
finject-injective {x} (suc y) fzero (fsuc b) f0≡fsb =
  absurd {A = λ _ → fzero ≡ fsuc b} (fzero≢fsuc (finject (suc y) b) f0≡fsb)
finject-injective {x} (suc y) (fsuc a) fzero fsa≡f0 =
  absurd {A = λ _ → fsuc a ≡ fzero} (fsuc≢fzero (finject (suc y) a) fsa≡f0)
finject-injective {x} (suc y) (fsuc a) (fsuc b) fsa≡fsb =
  cong fsuc (finject-injective (suc y) a b (fsuc-injective fsa≡fsb))

finject∘fsuc-commutes : ∀ {x y : ℕ} → (a : Fin x)
                      → finject y (fsuc a) ≡ fsuc (finject y a)
finject∘fsuc-commutes {suc x} {zero} a = refl
finject∘fsuc-commutes {suc x} {suc y} a = refl
finject∘fsuc-commutes {zero} {suc y} a = refl

fshift-injective : {x : ℕ} → (y : ℕ) → is-injective (fshift x {y})
fshift-injective {zero} y a b fa≡fb = fa≡fb
fshift-injective {suc x} y a b fa≡fb =
  fshift-injective {x} y a b (fsuc-injective fa≡fb)

fsuc-subst-reorder
  : ∀ {x y : ℕ} → (p : x ≡ y) → (a : Fin x)
  → (λ i → _)
    [ transport (λ i → Fin (suc (p i))) (fsuc a)
    ≡ fsuc (transport (λ i → Fin (p i)) a)
    ]
fsuc-subst-reorder p a = transport-reorder Fin suc fsuc p a

finject-subst-reorder
  : ∀ {x y : ℕ} (z : ℕ) (p : x ≡ y) (a : Fin x)
  → _
    [ subst (λ ○ → Fin (○ +ℕ z)) p (finject {x} z a)
    ≡ finject {y} z (subst Fin p a)
    ]
finject-subst-reorder z p a =
  transport-reorder Fin (_+ℕ z) (λ {w} b → finject {w} z b) p a
 
fshift-subst-reorder
  : ∀ {x y z : ℕ} → (p : x ≡ y) → (a : Fin x)
  → (λ i → _)
    [ subst (λ ○ → Fin (z +ℕ ○)) p (fshift z {x} a)
    ≡ fshift z {y} (subst Fin p a)
    ]
fshift-subst-reorder {x} {y} {z} p a =
  transport-reorder Fin (z +ℕ_) (λ {w} b → fshift z b) p a
