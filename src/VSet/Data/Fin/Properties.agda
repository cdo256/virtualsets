module VSet.Data.Fin.Properties where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ; +-zero) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Function.Injection

open ℕ.ℕ

private
  variable
    ℓ : Level
    x y z : ℕ
    a : Fin x
    b : Fin y

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

_≈?ᶠ_ : ∀ {x} → (a : Fin x) (b : Fin y) → Dec (a ≈ᶠ b)
a ≈?ᶠ b with (a ≟ᶠ b)
... | flt a<b = no (<ᶠ→≉ a<b)
... | feq a≈b = yes a≈b
... | fgt b<a = no (≉fsym (<ᶠ→≉ b<a))

_≡?ᶠ_ : ∀ {x} → Discrete (Fin x)
a ≡?ᶠ b with (a ≟ᶠ b)
... | flt a<b = no (≉ᶠ→≢ (<ᶠ→≉ a<b))
... | feq a≈b = yes (≈ᶠ→≡ a≈b)
... | fgt b<a = no (≢sym (≉ᶠ→≢ (<ᶠ→≉ b<a)))

isSetFin : ∀ {x} → isSet (Fin x)
isSetFin = Discrete→isSet _≡?ᶠ_

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

fsplice≉b : ∀ {x} → (b : Fin (suc x)) → (a : Fin x) → fsplice b a ≉ᶠ b
fsplice≉b fzero a = fsuc≉fzero
fsplice≉b (fsuc b) fzero = fzero≉fsuc
fsplice≉b (fsuc b) (fsuc a) ne = 
  let rec≉b = fsplice≉b b a
  in rec≉b (≈fsuc-injective ne)

≉fsuc
  : ∀ {x : ℕ} → {b a : Fin (suc x)} → (a≉b : a ≉ᶠ b)
  → fsuc a ≉ᶠ fsuc b
≉fsuc a≉b (≈fsuc a≈b) = a≉b a≈b

≉pred : ∀ {x y} {a : Fin x} {b : Fin y} → fsuc a ≉ᶠ fsuc b → a ≉ᶠ b
≉pred a'≉b' a≈b = a'≉b' (≈fsuc a≈b)

fsuc-funsplice 
  : ∀ {x : ℕ} → (b a : Fin (suc x)) → (a≉b : a ≉ᶠ b)
  → funsplice (fsuc b) (fsuc a) (≉fsuc a≉b)
  ≡ fsuc (funsplice b a a≉b)
fsuc-funsplice b        a a≉b with (a ≟ᶠ b)
fsuc-funsplice b        a a≉b | flt a<b = refl
fsuc-funsplice b        a a≉b | feq a≈b = absurd (a≉b a≈b)
fsuc-funsplice b (fsuc a) a≉b | fgt a>b = refl

funsplice-irrelevant
  : ∀ {x : ℕ} → (b a : Fin (suc x))
  → (u v : a ≉ᶠ b)
  → funsplice b a u ≡ funsplice b a v
funsplice-irrelevant b        a u v with (a ≟ᶠ b)
funsplice-irrelevant b        a u v | flt a<b = refl
funsplice-irrelevant b        a u v | feq a≈b = absurd (u a≈b)
funsplice-irrelevant b (fsuc a) u v | fgt a>b = refl

-- This could be simplified.
funsplice-fsplice-inverse
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x)
  → (splicea≉b : fsplice b a ≉ᶠ b)
  → funsplice b (fsplice b a) splicea≉b ≡ a
funsplice-fsplice-inverse {zero} fzero ()
funsplice-fsplice-inverse {suc zero} fzero fzero splicea≉b = refl
funsplice-fsplice-inverse {suc (suc x)} fzero fzero splicea≉b = refl
funsplice-fsplice-inverse {suc (suc x)} fzero (fsuc a) splicea≉b = refl
funsplice-fsplice-inverse {suc zero} (fsuc b) fzero splicea≉b = refl
funsplice-fsplice-inverse {suc (suc x)} (fsuc b) fzero splicea≉b = refl
funsplice-fsplice-inverse {suc (suc x)} (fsuc b) (fsuc a) splicea'≉b' =
  funsplice (fsuc b) (fsplice (fsuc b) (fsuc a)) splicea'≉b'  
    ≡⟨ refl ⟩
  funsplice (fsuc b) (fsuc (fsplice b a)) splicea'≉b'  
    ≡⟨ funsplice-irrelevant (fsuc b) (fsuc (fsplice b a))
       splicea'≉b' (≉fsuc (fsplice≉b b a)) ⟩
  funsplice (fsuc b) (fsuc (fsplice b a)) 
   (≉fsuc (fsplice≉b b a))
    ≡⟨ fsuc-funsplice b (fsplice b a) (fsplice≉b b a) ⟩
  fsuc (funsplice b (fsplice b a)
                  (fsplice≉b b a))
    ≡⟨ cong fsuc (funsplice-irrelevant b (fsplice b a)
        (fsplice≉b b a)
        (λ a≈b → fsplice≉b (fsuc b) (fsuc a) (≈fsuc a≈b))) ⟩
  fsuc (funsplice b (fsplice b a) 
                  (λ a≈b → fsplice≉b (fsuc b) (fsuc a) (≈fsuc a≈b)))
    ≡⟨ refl ⟩
  fsuc (funsplice b (fsplice b a) 
   (fsplice≉b b a))
    ≡⟨ cong fsuc (funsplice-fsplice-inverse b a (fsplice≉b b a)) ⟩
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

≤→fsplice≈suc : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
              → a2 ≤ᶠ finj a1 → fsplice a2 a1 ≈ᶠ fsuc a1
≤→fsplice≈suc fzero fzero a2≤a1 = {!!}
≤→fsplice≈suc fzero (fsuc a2) (inr a2'≈0) = absurd (fsuc≉fzero a2'≈0)
≤→fsplice≈suc (fsuc a1) fzero a2≤a1 = {!!}
≤→fsplice≈suc {suc m} (fsuc a1) (fsuc a2) rec-le =
  ≈fsuc (≤→fsplice≈suc a1 a2 (≤ᶠ-respects-pred rec-le))

>→fsplice≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → finj a1 <ᶠ a2 → fsplice a2 a1 ≈ᶠ finj a1
>→fsplice≈id fzero (fsuc a2) a1<a2 = ≈refl
>→fsplice≈id {suc m} (fsuc a1) (fsuc a2) a1<a2 =
  ≈fsuc (>→fsplice≈id a1 a2 (<ᶠ-respects-pred a1<a2))

-- antisplice : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
--            → Fin (suc x)
-- antisplice _ fzero = fzero
-- antisplice fzero (fsuc a) = a
-- antisplice {suc x} (fsuc b) (fsuc a) =
--   fsuc (antisplice b a)

<→antisplice≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 <ᶠ a1 → antisplice a1 a2 ≈ᶠ a2
<→antisplice≈id (fsuc a1) fzero a2<a1 = {!!}
<→antisplice≈id {suc m} (fsuc a1) (fsuc a2) (<fsuc a2<a1) =
  ≈fsuc (<→antisplice≈id a1 a2 a2<a1)

≈→antisplice≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≈ᶠ a1 → antisplice a1 a2 ≈ᶠ a2
≈→antisplice≈id fzero fzero _ = {!!}
≈→antisplice≈id (fsuc a1) fzero _ = {!!}
≈→antisplice≈id fzero (fsuc a2) a2'≈0 = absurd (fsuc≉fzero a2'≈0)
≈→antisplice≈id {suc m} (fsuc a1) (fsuc a2) a2≈a1 =
  ≈fsuc (≈→antisplice≈id a1 a2 (≈fsuc-injective a2≈a1))

≤→antisplice≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≤ᶠ a1 → antisplice a1 a2 ≈ᶠ a2
≤→antisplice≈id a1 a2 (inl a2<a1) = <→antisplice≈id a1 a2 a2<a1
≤→antisplice≈id a1 a2 (inr a2≈a1) = ≈→antisplice≈id a1 a2 a2≈a1

>→antisplice≈pred : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                  → finj a1 <ᶠ a2 → antisplice a1 a2 ≈ᶠ pred a2
>→antisplice≈pred fzero (fsuc a2) a2>a1 = ≈refl
>→antisplice≈pred {suc m} (fsuc a1) (fsuc (fsuc a2)) (<fsuc a2>a1) =
  ≈fsuc (>→antisplice≈pred a1 (fsuc a2) a2>a1)

fsplice≈case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → fsplice a2 a1 ≈ᶠ(case≤?ᶠ a2 (finj a1) (fsuc a1) (finj a1))
fsplice≈case a1 a2 with (a2 ≤?ᶠ finj a1)
... | fle a2≤a1 = ≤→fsplice≈suc a1 a2 a2≤a1
... | fgt a2>a1 = >→fsplice≈id a1 a2 a2>a1

-- antisplice≈case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
--                 → antisplice a1 a2
--                 ≈ᶠ case≤?ᶠ a2 (finj a1) a2 (finj (pred a2))
-- antisplice≈case a1 a2 with (a2 ≤?ᶠ a1)
-- ... | fle a2≤a1 = ≤→antisplice≈id a1 a2 a2≤a1
-- ... | fgt a2>a1 = cong finj (>→antisplice≈pred a1 a2 a2>a1)

finj∘fsuc≈fsuc∘finj : ∀ {x} (a : Fin (suc x)) → finj (fsuc a) ≈ᶠ fsuc (finj a)
finj∘fsuc≈fsuc∘finj a = ≈refl

splice-splice-antisplice 
  : ∀ {m} →  (b : Fin (suc (suc m))) → (c : Fin (suc m))
  → fsplice (fsplice b c) (antisplice c b)
  ≡ b
splice-splice-antisplice fzero fzero = refl
splice-splice-antisplice fzero (fsuc c) = refl
splice-splice-antisplice (fsuc b) fzero = refl
splice-splice-antisplice {m = suc m} (fsuc b) (fsuc c) =
  fsplice (fsplice (fsuc b) (fsuc c))
          (antisplice (fsuc c) (fsuc b))
    ≡⟨ refl ⟩
  fsplice (fsuc (fsplice b c))
          (fsuc (antisplice c b))
    ≡⟨ refl ⟩
  fsuc (fsplice (fsplice b c)
                (antisplice c b))
    ≡⟨ cong fsuc (splice-splice-antisplice b c) ⟩
  fsuc b ▯
