module VSet.Data.Fin.Properties where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ; +-zero; +-suc) renaming (_+_ to _+ℕ_)
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

subst-fsuc-reorder
  : ∀ {x y : ℕ} → (p : x ≡ y) → (a : Fin x)
  → transport (λ i → Fin (suc (p i))) (fsuc a)
  ≡ fsuc (transport (λ i → Fin (p i)) a)
subst-fsuc-reorder p a = transport-reorder Fin suc fsuc p a

fshift-fsuc-reorder : ∀ {x y : ℕ} → (a : Fin y)
                    → fshift x {suc y} (fsuc {y} a)
                    ≡ subst Fin (sym (ℕ.+-suc x y)) (fsuc (fshift x {y} a))
fshift-fsuc-reorder {zero} {suc y} a =
  fshift zero (fsuc a)
    ≡⟨ refl ⟩
  fsuc a
    ≡⟨ cong fsuc (sym (substRefl {B = Fin} a)) ⟩
  fsuc (subst Fin (sym (ℕ.+-suc 0 y)) a)
    ≡⟨ refl ⟩
  fsuc (subst Fin (sym (ℕ.+-suc 0 y)) (fshift 0 {suc y} a))
    ≡⟨ sym (subst-fsuc-reorder (λ i → ℕ.+-suc 0 y (~ i)) a) ⟩
  subst Fin (sym (ℕ.+-suc 0 (suc y))) (fsuc (fshift 0 {suc y} a)) ▯
fshift-fsuc-reorder {suc x} {suc y} a =
  fshift (suc x) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (fshift x (fsuc a))
    ≡⟨ {!!} ⟩
  subst Fin (sym (ℕ.+-suc (suc x) (suc y))) (fshift (suc (suc x)) a)
    ≡⟨ refl ⟩
  subst Fin (sym (ℕ.+-suc (suc x) (suc y))) (fsuc (fshift (suc x) a)) ▯

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

finj-injective : {x : ℕ} → is-injective (finj {x})
finj-injective fzero fzero fx≡fy = refl
finj-injective fzero (fsuc y) fx≡fy = absurd (fzero≢fsuc (finj y) fx≡fy)
finj-injective (fsuc x) fzero fx≡fy = absurd (fsuc≢fzero (finj x) fx≡fy)
finj-injective (fsuc x) (fsuc y) fx≡fy =
  cong fsuc (finj-injective x y (fsuc-injective fx≡fy))

-- Easier to do the dumb way. as in the suc y case.
finject-injective : {x : ℕ} → (y : ℕ) → is-injective (finject {x} y)
finject-injective {x} zero a b fa≡fb = 
  a
    ≡⟨ sym (subst⁻Subst Fin (sym (+-zero x)) a) ⟩
  subst Fin (+-zero x) (subst Fin (sym (+-zero x)) a)
    ≡⟨ cong (subst Fin (+-zero x)) (sym (finject0≡subst a)) ⟩
  subst Fin (+-zero x) (finject zero a)
    ≡⟨ cong (subst Fin (+-zero x)) fa≡fb ⟩
  subst Fin (+-zero x) (finject zero b)
    ≡⟨ cong (subst Fin (+-zero x)) (finject0≡subst b) ⟩
  subst Fin (+-zero x) (subst Fin (sym (+-zero x)) b)
    ≡⟨ subst⁻Subst Fin (sym (+-zero x)) b ⟩
  b ▯
finject-injective {x} (suc y) fzero fzero fa≡fb = refl
finject-injective {x} (suc y) fzero (fsuc b) fa≡fb = absurd (fzero≢fsuc (finject (suc y) b) fa≡fb)
finject-injective {x} (suc y) (fsuc a) fzero fa≡fb = absurd (fsuc≢fzero (finject (suc y) a) fa≡fb)
finject-injective {x} (suc y) (fsuc a) (fsuc b) fa≡fb =
  cong fsuc (finject-injective (suc y) a b (fsuc-injective fa≡fb))


fsuc-fjoin 
  : ∀ {x : ℕ} → (b a : Fin (suc x)) → (a≉b : a ≉ᶠ b)
  → fjoin (fsuc b) (fsuc a) (≉fsuc a≉b)
  ≡ fsuc (fjoin b a a≉b)
fsuc-fjoin b        a a≉b with (a ≟ᶠ b)
fsuc-fjoin b        a a≉b | flt a<b = refl
fsuc-fjoin b        a a≉b | feq a≈b = absurd (a≉b a≈b)
fsuc-fjoin b (fsuc a) a≉b | fgt a>b = refl

fjoin-irrelevant
  : ∀ {x : ℕ} → (b a : Fin (suc x))
  → (u v : a ≉ᶠ b)
  → fjoin b a u ≡ fjoin b a v
fjoin-irrelevant b        a u v with (a ≟ᶠ b)
fjoin-irrelevant b        a u v | flt a<b = refl
fjoin-irrelevant b        a u v | feq a≈b = absurd (u a≈b)
fjoin-irrelevant b (fsuc a) u v | fgt a>b = refl

fjoin-cong
  : ∀ {x} → {b1 b2 a1 a2 : Fin (suc x)}
  → (p : b1 ≡ b2) → (q : a1 ≡ a2)
  → (ne : a1 ≉ᶠ b1)
  → fjoin b1 a1 ne ≡ fjoin b2 a2 (subst2 _≉ᶠ_ q p ne)
fjoin-cong {b1 = b1} {b2} {a1} {a2} p q ne i =
  fjoin (p i) (q i) (subst2-filler _≉ᶠ_ q p ne i)

-- This could be simplified.
fjoin-fsplice-inverse
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x)
  → (fsplicea≉b : fsplice b a ≉ᶠ b)
  → fjoin b (fsplice b a) fsplicea≉b ≡ a
fjoin-fsplice-inverse {zero} fzero ()
fjoin-fsplice-inverse {suc zero} fzero fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} fzero fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} fzero (fsuc a) fsplicea≉b = refl
fjoin-fsplice-inverse {suc zero} (fsuc b) fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} (fsuc b) fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} (fsuc b) (fsuc a) fsplicea'≉b' =
  fjoin (fsuc b) (fsplice (fsuc b) (fsuc a)) fsplicea'≉b'  
    ≡⟨ refl ⟩
  fjoin (fsuc b) (fsuc (fsplice b a)) fsplicea'≉b'  
    ≡⟨ fjoin-irrelevant (fsuc b) (fsuc (fsplice b a))
       fsplicea'≉b' (≉fsuc (fsplice≉b b a)) ⟩
  fjoin (fsuc b) (fsuc (fsplice b a)) 
   (≉fsuc (fsplice≉b b a))
    ≡⟨ fsuc-fjoin b (fsplice b a) (fsplice≉b b a) ⟩
  fsuc (fjoin b (fsplice b a)
                  (fsplice≉b b a))
    ≡⟨ cong fsuc (fjoin-irrelevant b (fsplice b a)
        (fsplice≉b b a)
        (λ a≈b → fsplice≉b (fsuc b) (fsuc a) (≈fsuc a≈b))) ⟩
  fsuc (fjoin b (fsplice b a) 
                  (λ a≈b → fsplice≉b (fsuc b) (fsuc a) (≈fsuc a≈b)))
    ≡⟨ refl ⟩
  fsuc (fjoin b (fsplice b a) 
   (fsplice≉b b a))
    ≡⟨ cong fsuc (fjoin-fsplice-inverse b a (fsplice≉b b a)) ⟩
  fsuc a ▯

fsplice-isInjective
  : ∀ {m} {a : Fin (suc m)} {b c : Fin m}
  → fsplice a b ≡ fsplice a c → b ≡ c
fsplice-isInjective {a = a} {fzero} {fzero} fsplice-eq = refl
fsplice-isInjective {a = fzero} {b} {c} fsplice-eq = fsuc-injective fsplice-eq
fsplice-isInjective {a = fsuc a} {fzero} {fsuc c} fsplice-eq =
  absurd {A = λ _ → fzero ≡ fsuc c}
         (fzero≢fsuc (fsplice a c) fsplice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fzero} fsplice-eq =
  absurd {A = λ _ → fsuc b ≡ fzero}
         (fsuc≢fzero (fsplice a b) fsplice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fsuc c} fsplice-eq =
  cong fsuc $ fsplice-isInjective (fsuc-injective fsplice-eq)

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

<→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 <ᶠ a1 → fcross a1 a2 ≈ᶠ a2
<→fcross≈id (fsuc a1) fzero a2<a1 = {!!}
<→fcross≈id {suc m} (fsuc a1) (fsuc a2) (<fsuc a2<a1) =
  ≈fsuc (<→fcross≈id a1 a2 a2<a1)

≈→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≈ᶠ a1 → fcross a1 a2 ≈ᶠ a2
≈→fcross≈id fzero fzero _ = {!!}
≈→fcross≈id (fsuc a1) fzero _ = {!!}
≈→fcross≈id fzero (fsuc a2) a2'≈0 = absurd (fsuc≉fzero a2'≈0)
≈→fcross≈id {suc m} (fsuc a1) (fsuc a2) a2≈a1 =
  ≈fsuc (≈→fcross≈id a1 a2 (≈fsuc-injective a2≈a1))

≤→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≤ᶠ a1 → fcross a1 a2 ≈ᶠ a2
≤→fcross≈id a1 a2 (inl a2<a1) = <→fcross≈id a1 a2 a2<a1
≤→fcross≈id a1 a2 (inr a2≈a1) = ≈→fcross≈id a1 a2 a2≈a1

>→fcross≈pred : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                  → finj a1 <ᶠ a2 → fcross a1 a2 ≈ᶠ pred a2
>→fcross≈pred fzero (fsuc a2) a2>a1 = ≈refl
>→fcross≈pred {suc m} (fsuc a1) (fsuc (fsuc a2)) (<fsuc a2>a1) =
  ≈fsuc (>→fcross≈pred a1 (fsuc a2) a2>a1)

fsplice≈case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → fsplice a2 a1 ≈ᶠ(case≤?ᶠ a2 (finj a1) (fsuc a1) (finj a1))
fsplice≈case a1 a2 with (a2 ≤?ᶠ finj a1)
... | fle a2≤a1 = ≤→fsplice≈suc a1 a2 a2≤a1
... | fgt a2>a1 = >→fsplice≈id a1 a2 a2>a1

-- fcross≈case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
--                 → fcross a1 a2
--                 ≈ᶠ case≤?ᶠ a2 (finj a1) a2 (finj (pred a2))
-- fcross≈case a1 a2 with (a2 ≤?ᶠ a1)
-- ... | fle a2≤a1 = ≤→fcross≈id a1 a2 a2≤a1
-- ... | fgt a2>a1 = cong finj (>→fcross≈pred a1 a2 a2>a1)

finj∘fsuc≈fsuc∘finj : ∀ {x} (a : Fin (suc x)) → finj (fsuc a) ≈ᶠ fsuc (finj a)
finj∘fsuc≈fsuc∘finj a = ≈refl

fsplice-fsplice-fcross 
  : ∀ {m} →  (b : Fin (suc (suc m))) → (c : Fin (suc m))
  → fsplice (fsplice b c) (fcross c b)
  ≡ b
fsplice-fsplice-fcross fzero fzero = refl
fsplice-fsplice-fcross fzero (fsuc c) = refl
fsplice-fsplice-fcross (fsuc b) fzero = refl
fsplice-fsplice-fcross {m = suc m} (fsuc b) (fsuc c) =
  fsplice (fsplice (fsuc b) (fsuc c))
          (fcross (fsuc c) (fsuc b))
    ≡⟨ refl ⟩
  fsplice (fsuc (fsplice b c))
          (fsuc (fcross c b))
    ≡⟨ refl ⟩
  fsuc (fsplice (fsplice b c)
                (fcross c b))
    ≡⟨ cong fsuc (fsplice-fsplice-fcross b c) ⟩
  fsuc b ▯

fjoin-fsplice-fsplice-fcross-fsplice
  : ∀ {n} → (b : Fin (suc (suc n)))
  → (c : Fin (suc n))
  → (ne : fsplice b c ≉ᶠ fsplice (fsplice b c) (fcross c b))
  → fjoin (fsplice (fsplice b c) (fcross c b)) (fsplice b c) ne
  ≡ fjoin b (fsplice b c)
              (subst (fsplice b c ≉ᶠ_)
                     (fsplice-fsplice-fcross b c) ne)
fjoin-fsplice-fsplice-fcross-fsplice b c ne i
  = fjoin (fsplice-fsplice-fcross b c i) (fsplice b c)
              (subst-filler (fsplice b c ≉ᶠ_) (fsplice-fsplice-fcross b c) ne i)

fjoin-fsplice'
  : ∀ {n} → (b : Fin (suc n))
  → (c : Fin (suc (suc n))) 
  → (ne : c ≉ᶠ fsplice' c b)
  → (fjoin (fsplice' c b) c ne)
  ≡ fcross' b c
fjoin-fsplice' b c ne with c ≤?ᶠ b
fjoin-fsplice' b c ne | fle c≤b =
  fjoin (fsplice'-cases c b (fle c≤b)) c ne
    ≡⟨ refl ⟩
  fjoin-cases (fsuc b) c ne (c ≟ᶠ fsuc b)
    ≡⟨ cong (fjoin-cases (fsuc b) c ne)
            (isPropTrichotomyᶠ (c ≟ᶠ fsuc b) (flt (≤ᶠ→<ᶠ c≤b))) ⟩
  fjoin-cases (fsuc b) c ne (flt (≤ᶠ→<ᶠ c≤b))
    ≡⟨ refl ⟩
  fin-restrict-< c (≤ᶠ→<ᶠ c≤b)
    ≡⟨ refl ⟩
  fin-restrict-≤ c c≤b
    ≡⟨ refl ⟩
  fcross'-cases b c (fle c≤b) ▯
fjoin-fsplice' b (fsuc c) ne | fgt c>b =
  fjoin-cases (fsplice'-cases (fsuc c) b (fgt c>b)) (fsuc c) ne
                  (fsuc c ≟ᶠ fsplice'-cases (fsuc c) b (fgt c>b))
    ≡⟨ refl ⟩
  fjoin-cases (finj b) (fsuc c) ne (fsuc c ≟ᶠ finj b)
    ≡⟨ cong (fjoin-cases (finj b) (fsuc c) ne)
              (isPropTrichotomyᶠ (fsuc c ≟ᶠ finj b) (fgt (<ᶠ-inj-l c>b))) ⟩
  fjoin-cases (finj b) (fsuc c) ne (fgt (<ᶠ-inj-l c>b))
    ≡⟨ refl ⟩
  c
    ≡⟨ refl ⟩
  pred (fsuc c)
    ≡⟨ refl ⟩
  fcross'-cases b (fsuc c) (fgt c>b) ▯

fjoin-fsplice-fsplice-fsplice
  : ∀ {n} → (a : Fin (suc (suc n))) → (b : Fin (suc n))
  → (c : Fin (suc n)) 
  → (ne : fsplice a c ≉ᶠ fsplice (fsplice a c) b)
  → (fjoin (fsplice (fsplice a c) b) (fsplice a c) ne)
  ≡ fcross b (fsplice a c)
fjoin-fsplice-fsplice-fsplice a b c ne =
  fjoin (fsplice (fsplice a c) b) (fsplice a c) ne
    ≡⟨ fjoin-cong (fsplice≡fsplice' (fsplice a c) b) refl ne ⟩
  fjoin (fsplice' (fsplice a c) b) (fsplice a c) _
    ≡⟨ fjoin-fsplice' b (fsplice a c) _ ⟩
  fcross' b (fsplice a c)
    ≡⟨ sym (fcross≡fcross' b (fsplice a c)) ⟩
  fcross b (fsplice a c) ▯

fsplice-fsplice-fsplice-fcross
  : ∀ {m} → (b : Fin (suc (suc m))) → (a : Fin m) → (c : Fin (suc m)) 
  → fsplice (fsplice b c) (fsplice (fcross c b) a)
  ≡ fsplice b (fsplice c a)
fsplice-fsplice-fsplice-fcross fzero fzero fzero = refl
fsplice-fsplice-fsplice-fcross fzero fzero (fsuc c) = refl
fsplice-fsplice-fsplice-fcross fzero (fsuc a) fzero = refl
fsplice-fsplice-fsplice-fcross fzero (fsuc a) (fsuc c) = refl
fsplice-fsplice-fsplice-fcross (fsuc b) fzero fzero = refl
fsplice-fsplice-fsplice-fcross (fsuc b) fzero (fsuc c) = refl
fsplice-fsplice-fsplice-fcross (fsuc b) (fsuc a) fzero = refl
fsplice-fsplice-fsplice-fcross (fsuc b) (fsuc a) (fsuc c) =
  cong fsuc (fsplice-fsplice-fsplice-fcross b a c)

fcross-fcross-fsplice
  : ∀ {m} → (b : Fin (suc (suc m))) (c : Fin (suc m))
  → (fcross (fcross c b) (fsplice b c)) ≡ c
fcross-fcross-fsplice fzero fzero = refl
fcross-fcross-fsplice fzero (fsuc c) = refl
fcross-fcross-fsplice (fsuc b) fzero = refl
fcross-fcross-fsplice {m = suc m} (fsuc b) (fsuc c) =
  cong fsuc (fcross-fcross-fsplice b c)
