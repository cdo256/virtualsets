module VSet.Data.Fin.Properties where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ; +-zero) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
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
toℕ∘fromℕ≡id {zero} n n<0 =
  absurd {A = λ _ → toℕ {zero} (fromℕ n n<0) ≡ n}
         (¬-<-zero {n} n<0)
toℕ∘fromℕ≡id {suc m} zero 0<sm = refl
toℕ∘fromℕ≡id {suc m} (suc n) sn<sm =
  cong suc (toℕ∘fromℕ≡id n (pred-<-pred sn<sm))

toℕ<m : ∀ {m : ℕ} → (a : Fin m) → toℕ a < m 
toℕ<m {suc m} fzero = 0<suc m
toℕ<m {suc m} (fsuc a) = suc-<-suc (toℕ<m a)

fsuc-injective : ∀ {n} {i j : Fin n} → fsuc {n} i ≡ fsuc {n} j → i ≡ j
fsuc-injective {zero} {()} {()} 
fsuc-injective {suc n} {i} {j} p = cong pred p

<ᶠ→≢ : ∀ {x} → {a b : Fin x} → a <ᶠ b → a ≢ b
<ᶠ→≢ {a = fzero} {b = fsuc b} <fzero a≡b = fzero≢fsuc b a≡b
<ᶠ→≢ {a = fsuc a} {b = fsuc b} (<fsuc a<b) a≡b =
  <ᶠ→≢ {a = a} {b = b} a<b (fsuc-injective a≡b)

<ᶠ-respects-pred : ∀ {x} → {a b : Fin x} → fsuc a <ᶠ fsuc b → a <ᶠ b
<ᶠ-respects-pred (<fsuc a'<b') = a'<b'

≤ᶠ-respects-pred : ∀ {x} → {a b : Fin x} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤ᶠ-respects-pred (inl a'<b') = inl (<ᶠ-respects-pred a'<b')
≤ᶠ-respects-pred (inr a'≡b') = inr (fsuc-injective a'≡b')

-- finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x +ℕ y)
-- finject {suc x} zero fzero = fzero
-- finject {suc x} zero (fsuc a) = fsuc (finject zero a)
-- finject {suc x} (suc y) fzero = fzero
-- finject {suc x} (suc y) (fsuc a) = fsuc (finject {x} (suc y) a)

-- fzero-subst : {x y : ℕ} (p : suc x ≡ suc y) (a : Fin x)
--             → (λ i → {!!} i) [ fzero {n = y} ≡ subst Fin p (fzero {n = x}) ]
-- fzero-subst {x} {y} p a =
--   fzero {n = y} ≡P[ {!!} ][ p ∙P refl ]⟨ Fin ➢ {!!} ⟩ (subst Fin p (fzero {n = x}) ∎P)

finject-fsuc-reorder : ∀ {x y : ℕ} → (a : Fin x)
                      → finject y (fsuc a) ≡ fsuc (finject y a)
finject-fsuc-reorder {suc x} {zero} a = refl
finject-fsuc-reorder {suc x} {suc y} a = refl
finject-fsuc-reorder {zero} {suc y} a = refl

finject0≡subst : {x : ℕ} (a : Fin x)
               → finject {x} zero a ≡ subst Fin (sym (+-zero x)) a
finject0≡subst {suc x} fzero =
  resubst (Fin ∘ suc) (λ z → fzero {z}) (sym (+-zero x))
finject0≡subst {suc x} (fsuc a) =
  finject zero (fsuc a) ≡⟨ finject-fsuc-reorder a ⟩
  fsuc (finject zero a) ≡⟨ cong fsuc (finject0≡subst a) ⟩
  fsuc (subst Fin (sym (+-zero x)) a)
    ≡⟨ sym (transport-reorder Fin suc fsuc (sym (+-zero x)) a) ⟩
  subst Fin (sym (+-zero (suc x))) (fsuc a) ▯

finject-injective : {x : ℕ} → (y : ℕ) → is-injective (finject {x} y)
finject-injective {x} zero a b fa≡fb = 
  let step1 : finject zero ≡ subst Fin (sym (+-zero x))
      step1 = funExt finject0≡subst
  in a
       ≡⟨ sym (subst⁻Subst Fin (sym (+-zero x)) a) ⟩
     subst Fin (+-zero x) (subst Fin (sym (+-zero x)) a)
       ≡⟨ cong (subst Fin (+-zero x)) (sym (finject0≡subst a)) ⟩
     subst Fin (+-zero x) (finject zero a)
       ≡⟨ cong (subst Fin (+-zero x)) fa≡fb ⟩
     subst Fin (+-zero x) (finject zero b)
       ≡⟨ cong (subst Fin (+-zero x)) (finject0≡subst b) ⟩
     subst Fin (+-zero x) (subst Fin (sym (+-zero x)) b)
       ≡⟨ (subst⁻Subst Fin (sym (+-zero x)) b) ⟩
     b ▯
finject-injective {x} (suc y) fzero fzero _ = refl
finject-injective {x} (suc y) fzero (fsuc b) f0≡fsb =
  absurd {A = λ _ → fzero ≡ fsuc b} (fzero≢fsuc (finject (suc y) b) f0≡fsb)
finject-injective {x} (suc y) (fsuc a) fzero fsa≡f0 =
  absurd {A = λ _ → fsuc a ≡ fzero} (fsuc≢fzero (finject (suc y) a) fsa≡f0)
finject-injective {x} (suc y) (fsuc a) (fsuc b) fsa≡fsb =
  cong fsuc (finject-injective (suc y) a b (fsuc-injective fsa≡fsb))

subst-fsuc-reorder
  : ∀ {x y : ℕ} → (p : x ≡ y) → (a : Fin x)
  → transport (λ i → Fin (suc (p i))) (fsuc a)
  ≡ fsuc (transport (λ i → Fin (p i)) a)
subst-fsuc-reorder p a = transport-reorder Fin suc fsuc p a

-- fshift-fsuc-reorder : ∀ {x y : ℕ} → (a : Fin y)
--                     → fshift x {suc y} (fsuc {y} a)
--                     ≡ subst Fin (sym (ℕ.+-suc x y)) (fsuc (fshift x {y} a))
-- fshift-fsuc-reorder {zero} {suc y} a =
--   fshift zero (fsuc a)
--     ≡⟨ refl ⟩
--   fsuc a
--     ≡⟨ cong fsuc (sym (substRefl {B = Fin} a)) ⟩
--   fsuc (subst Fin (sym (ℕ.+-suc 0 y)) a)
--     ≡⟨ refl ⟩
--   fsuc (subst Fin (sym (ℕ.+-suc 0 y)) (fshift 0 {suc y} a))
--     ≡⟨ sym (subst-fsuc-reorder (λ i → ℕ.+-suc 0 y (~ i)) a) ⟩
--   subst Fin (sym (ℕ.+-suc 0 (suc y))) (fsuc (fshift 0 {suc y} a)) ▯
-- fshift-fsuc-reorder {suc x} {suc y} a =
--   fshift (suc x) (fsuc a)
--     ≡⟨ refl ⟩
--   fsuc (fshift x (fsuc a))
--     ≡⟨ {!!} ⟩
--   subst Fin (sym (ℕ.+-suc (suc x) (suc y))) (fshift (suc (suc x)) a)
--     ≡⟨ refl ⟩
--   subst Fin (sym (ℕ.+-suc (suc x) (suc y))) (fsuc (fshift (suc x) a)) ▯

fshift-injective : {x : ℕ} → (y : ℕ) → is-injective (fshift x {y})
fshift-injective {zero} y a b fa≡fb = fa≡fb
fshift-injective {suc x} y a b fa≡fb =
  fshift-injective {x} y a b (fsuc-injective fa≡fb)

subst-finject-reorder
  : ∀ {x y : ℕ} (z : ℕ) (p : x ≡ y) (a : Fin x)
  → subst (λ ○ → Fin (○ +ℕ z)) p (finject {x} z a)
  ≡ finject {y} z (subst Fin p a)
subst-finject-reorder z p a =
  transport-reorder Fin (_+ℕ z) (λ {w} b → finject {w} z b) p a
 
subst-fshift-reorder
  : ∀ {x y z : ℕ} → (p : x ≡ y) → (a : Fin x)
  → subst (λ ○ → Fin (z +ℕ ○)) p (fshift z {x} a)
  ≡ fshift z {y} (subst Fin p a)
subst-fshift-reorder {x} {y} {z} p a =
  transport-reorder Fin (z +ℕ_) (λ {w} b → fshift z b) p a

fzero-cong : {x y : ℕ} (p : x ≡ y)
           → (λ i → Fin (suc (p i))) [ fzero {x} ≡ fzero {y} ]
fzero-cong {x} {y} p i = fzero {p i}

fzero≡subst-fzero : {x y : ℕ} (p : x ≡ y)
                  → fzero {y} ≡ subst (Fin ∘ suc) p (fzero {x})
fzero≡subst-fzero {x} {y} p = resubst (Fin ∘ suc) (λ z → fzero {z}) p

fsplice≢b : ∀ {x} → (b : Fin (suc x)) → (a : Fin x) → fsplice b a ≢ b
fsplice≢b fzero a = fsuc≢fzero a
fsplice≢b (fsuc b) fzero = fzero≢fsuc b
fsplice≢b (fsuc b) (fsuc a) ne = 
  let rec≢b = fsplice≢b b a
  in rec≢b (fsuc-injective ne)

funsplice-fsplice-inverse
  : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc x))
  → funsplice b (fsplice b a) (fsplice≢b b a) ≡ a
funsplice-fsplice-inverse {zero} fzero fzero = refl
funsplice-fsplice-inverse {suc x} fzero fzero = refl
funsplice-fsplice-inverse {suc x} fzero (fsuc a) = refl
funsplice-fsplice-inverse {zero} (fsuc b) fzero = refl
funsplice-fsplice-inverse {suc x} (fsuc b) fzero = refl
funsplice-fsplice-inverse {suc x} (fsuc b) (fsuc a) =
  funsplice (fsuc b) (fsplice (fsuc b) (fsuc a))
   (fsplice≢b (fsuc b) (fsuc a))
    ≡⟨ refl ⟩
  funsplice (fsuc b) (fsuc (fsplice b a)) 
   (fsplice≢b (fsuc b) (fsuc a))
    ≡⟨ refl ⟩
  fsuc (funsplice b (fsplice b a) 
   (λ a≡b → fsplice≢b (fsuc b) (fsuc a) (cong fsuc a≡b)))
    ≡⟨ refl ⟩
  fsuc (funsplice b (fsplice b a) 
   (fsplice≢b b a))
    ≡⟨ cong fsuc (funsplice-fsplice-inverse b a) ⟩
  fsuc a ▯

fsplice-isInjective
  : ∀ {m} {a : Fin (suc m)} {b c : Fin m}
  → fsplice a b ≡ fsplice a c → b ≡ c
fsplice-isInjective {a = a} {fzero} {fzero} splice-eq = refl
fsplice-isInjective {a = fzero} {b} {c} splice-eq = fsuc-injective splice-eq
fsplice-isInjective {a = fsuc a} {fzero} {fsuc c} splice-eq =
  absurd {A = λ _ → fzero ≡ fsuc c}
         (fzero≢fsuc (fsplice a c) splice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fzero} splice-eq =
  absurd {A = λ _ → fsuc b ≡ fzero}
         (fsuc≢fzero (fsplice a b) splice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fsuc c} splice-eq =
  cong fsuc $ fsplice-isInjective (fsuc-injective splice-eq)

≤→fsplice≡suc : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
              → a2 ≤ᶠ finj a1 → fsplice a2 a1 ≡ fsuc a1
≤→fsplice≡suc fzero fzero a2≤a1 = refl
≤→fsplice≡suc fzero (fsuc a2) (inr a2'≡0) = absurd (fsuc≢fzero a2 a2'≡0)
≤→fsplice≡suc (fsuc a1) fzero a2≤a1 = refl
≤→fsplice≡suc {suc m} (fsuc a1) (fsuc a2) rec-le =
  cong fsuc (≤→fsplice≡suc a1 a2 (≤ᶠ-respects-pred rec-le))

>→fsplice≡id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → finj a1 <ᶠ a2 → fsplice a2 a1 ≡ finj a1
>→fsplice≡id fzero (fsuc a2) a1<a2 = refl
>→fsplice≡id {suc m} (fsuc a1) (fsuc a2) a1<a2 =
  cong fsuc (>→fsplice≡id a1 a2 (<ᶠ-respects-pred a1<a2))

-- antisplice : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
--            → Fin (suc x)
-- antisplice _ fzero = fzero
-- antisplice fzero (fsuc a) = a
-- antisplice {suc x} (fsuc b) (fsuc a) =
--   fsuc (antisplice b a)

<→antisplice≡id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 <ᶠ finj a1 → finj (antisplice a1 a2) ≡ a2
<→antisplice≡id (fsuc a1) fzero a2<a1 = refl
<→antisplice≡id {suc m} (fsuc a1) (fsuc a2) (<fsuc a2<a1) =
  cong fsuc (<→antisplice≡id a1 a2 a2<a1)

≡→antisplice≡id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≡ finj a1 → finj (antisplice a1 a2) ≡ a2
≡→antisplice≡id fzero fzero _ = refl
≡→antisplice≡id (fsuc a1) fzero _ = refl
≡→antisplice≡id fzero (fsuc a2) a2'≡0 = absurd (fsuc≢fzero a2 a2'≡0)
≡→antisplice≡id {suc m} (fsuc a1) (fsuc a2) a2≡a1 =
  cong fsuc (≡→antisplice≡id a1 a2 (fsuc-injective a2≡a1))

≤→antisplice≡id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≤ᶠ finj a1 → finj (antisplice a1 a2) ≡ a2
≤→antisplice≡id a1 a2 (inl a2<a1) = <→antisplice≡id a1 a2 a2<a1
≤→antisplice≡id a1 a2 (inr a2≡a1) = ≡→antisplice≡id a1 a2 a2≡a1

>→antisplice≡pred : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                  → finj a1 <ᶠ a2 → antisplice a1 a2 ≡ pred a2
>→antisplice≡pred fzero (fsuc a2) a2>a1 = refl
>→antisplice≡pred {suc m} (fsuc a1) (fsuc (fsuc a2)) (<fsuc a2>a1) =
  cong fsuc (>→antisplice≡pred a1 (fsuc a2) a2>a1)

case≤?ᶠ : {A : Type} {m : ℕ} (a b : Fin m) → A → A → A
case≤?ᶠ a b x y = case (a ≤?ᶠ b) of
  λ{ (fle _) → x
   ; (fgt _) → y }

fsplice≡case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → fsplice a2 a1 ≡ (case≤?ᶠ a2 (finj a1) (fsuc a1) (finj a1))
fsplice≡case a1 a2 with (a2 ≤?ᶠ finj a1)
... | fle a2≤a1 = ≤→fsplice≡suc a1 a2 a2≤a1
... | fgt a2>a1 = >→fsplice≡id a1 a2 a2>a1

antisplice≡case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → finj (antisplice a1 a2)
                ≡ (case≤?ᶠ a2 (finj a1) a2 (finj (pred a2)))
antisplice≡case a1 a2 with (a2 ≤?ᶠ finj a1)
... | fle a2≤a1 = ≤→antisplice≡id a1 a2 a2≤a1
... | fgt a2>a1 = cong finj (>→antisplice≡pred a1 a2 a2>a1)
