module VSet.Data.Fin.Properties where

open import VSet.Prelude
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ; +-zero; +-suc) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order
open import VSet.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.Fin.Minus


open ℕ.ℕ

private
  variable
    ℓ : Level
    x y z : ℕ
    a : Fin x
    b : Fin y

toℕ∘fromℕ≡id : {m : ℕ} → (n : ℕ) → (n<m : n < m) → toℕ {m} (fromℕ n n<m) ≡ n
toℕ∘fromℕ≡id {zero} n n<0 =
  absurd (¬-<-zero {n} n<0)
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

-- Like subst but computes on constructors. See std library.
fcast : (x ≡ y) → Fin x → Fin y
fcast {x = zero} {y = zero} p a = a
fcast {x = zero} {y = suc y} p a = absurd (ℕ.znots p)
fcast {x = suc x} {y = zero} p a = absurd (ℕ.snotz p)
fcast {x = suc x} {y = suc y} p fzero = fzero
fcast {x = suc x} {y = suc y} p (fsuc a) = fsuc (fcast (ℕ.injSuc p) a)

fcast-loop : (p : x ≡ x) → (a : Fin x) → fcast p a ≡ a
fcast-loop p fzero = refl
fcast-loop p (fsuc a) =
  cong fsuc (fcast-loop (cong ℕ.predℕ p) a)

fcast-irrelevant : (p q : x ≡ y) → (a : Fin x) → fcast p a ≡ fcast q a
fcast-irrelevant {x = zero} {y = zero} p q a = refl
fcast-irrelevant {x = zero} {y = suc y} p q a = absurd (ℕ.znots p)
fcast-irrelevant {x = suc x} {y = zero} p q a = absurd (ℕ.snotz p)
fcast-irrelevant {x = suc x} {y = suc y} p q fzero = refl
fcast-irrelevant {x = suc x} {y = suc y} p q (fsuc a) =
  cong fsuc (fcast-irrelevant (ℕ.injSuc p) (ℕ.injSuc q) a)

finject0≡fcast : {x : ℕ} (a : Fin x)
               → finject {x} zero a ≡ fcast (sym (+-zero x)) a
finject0≡fcast fzero = refl
finject0≡fcast (fsuc a) = cong fsuc (finject0≡fcast a)

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
    ≡⟨ cong fsuc (fshift-fsuc-reorder a) ⟩
  fsuc (subst Fin (sym (ℕ.+-suc (x) (suc y))) (fshift (suc x) a))
    ≡⟨ sym (subst-fsuc-reorder (sym (ℕ.+-suc (x) (suc y))) (fshift (suc x) a)) ⟩
  subst Fin (cong suc (sym (ℕ.+-suc (x) (suc y)))) (fsuc (fshift (suc x) a))
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

fzero≡cast-fzero : {x y : ℕ} (p : x ≡ y)
                 → fzero {y} ≡ fcast (cong suc p) (fzero {x})
fzero≡cast-fzero p = refl

ℕ+1 : ∀ {x : ℕ} → x ℕ.+ 1 ≡ suc x
ℕ+1 {x} = ℕ.+-comm x 1

finject1≡finj : {x : ℕ} (a : Fin x)
               → finject 1 a ≡ subst Fin (sym ℕ+1) (finj a)
finject1≡finj {suc x} fzero = fzero≡subst-fzero (sym ℕ+1)
finject1≡finj {suc x} (fsuc a) =
  finject 1 (fsuc a) ≡⟨ finject-fsuc-reorder a ⟩
  fsuc (finject 1 a) ≡⟨ cong fsuc (finject1≡finj a) ⟩
  fsuc (subst Fin (sym ℕ+1) (finj a)) ≡⟨ sym (subst-fsuc-reorder (sym ℕ+1) (finj a)) ⟩
  subst Fin (sym ℕ+1) (fsuc (finj a)) ≡⟨ refl ⟩
  subst Fin (sym ℕ+1) (finj (fsuc a)) ▯

finject1≡finj' : {x : ℕ} (a : Fin x)
              → finject 1 a ≡ fcast (ℕ.+-comm 1 x) (finj a)
finject1≡finj' {zero} ()
finject1≡finj' {suc x} fzero = refl
finject1≡finj' {suc x} (fsuc a) =
  finject 1 (fsuc a) ≡⟨ refl ⟩
  fsuc (finject 1 a) ≡⟨ cong fsuc (finject1≡finj' a) ⟩
  fsuc (fcast (ℕ.+-comm 1 x) (finj a))
    ≡⟨ cong fsuc ((fcast-irrelevant (ℕ.+-comm 1 x) ((ℕ.injSuc ((λ i → suc (suc x)) ∙ (λ i → suc (ℕ.+-comm 1 x i))))) (finj a))) ⟩
  fcast (ℕ.+-comm 1 (suc x)) (fsuc (finj a)) ≡⟨ refl ⟩
  fcast (ℕ.+-comm 1 (suc x)) (finj (fsuc a)) ▯

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
finj-injective fzero (fsuc y) fx≡fy = absurd (fzero≢fsuc fx≡fy)
finj-injective (fsuc x) fzero fx≡fy = absurd (fsuc≢fzero fx≡fy)
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
finject-injective {x} (suc y) fzero (fsuc b) fa≡fb = absurd (fzero≢fsuc fa≡fb)
finject-injective {x} (suc y) (fsuc a) fzero fa≡fb = absurd (fsuc≢fzero fa≡fb)
finject-injective {x} (suc y) (fsuc a) (fsuc b) fa≡fb =
  cong fsuc (finject-injective (suc y) a b (fsuc-injective fa≡fb))

toℕ-finject : {x : ℕ} (y : ℕ) (a : Fin x) → toℕ (finject y a) ≡ toℕ a
toℕ-finject y fzero = refl
toℕ-finject y (fsuc a) = cong suc (toℕ-finject y a)

toℕ-fshift : (x : ℕ) {y : ℕ}  (a : Fin y) → toℕ (fshift x a) ≡ toℕ a ℕ.+ x
toℕ-fshift zero fzero = refl
toℕ-fshift (suc x) fzero = cong suc (toℕ-fshift x f0)
toℕ-fshift zero (fsuc a) = cong suc (sym (+-zero (toℕ a)))
toℕ-fshift (suc x) (fsuc a) = cong suc u
  where
    u : toℕ (fshift x (fsuc a)) ≡ toℕ a +ℕ suc x
    u = toℕ (fshift x (fsuc a)) ≡⟨ toℕ-fshift x (fsuc a) ⟩
        suc (toℕ a) +ℕ x ≡⟨ sym (+-suc (toℕ a) x) ⟩
        toℕ a +ℕ suc x ▯

toℕ-finject-< : {x : ℕ} (y : ℕ) (a : Fin x) → toℕ (finject y a) < x
toℕ-finject-< {suc x} y fzero = 0<suc x
toℕ-finject-< {suc x} y (fsuc a) = suc-<-suc (toℕ-finject-< y a)

toℕ-fshift-≥ : (x : ℕ) {y : ℕ} (a : Fin y) → toℕ (fshift x a) ≥ x 
toℕ-fshift-≥ zero a = zero-≤
toℕ-fshift-≥ (suc x) a = suc-≤-suc (toℕ-fshift-≥ x a)

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
  absurd (fzero≢fsuc fsplice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fzero} fsplice-eq =
  absurd (fsuc≢fzero fsplice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fsuc c} fsplice-eq =
  cong fsuc $ fsplice-isInjective (fsuc-injective fsplice-eq)

≤→fsplice≈suc : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
              → a2 ≤ᶠ finj a1 → fsplice a2 a1 ≈ᶠ fsuc a1
≤→fsplice≈suc fzero fzero a2≤a1 = ≈fsuc ≈fzero
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
<→fcross≈id (fsuc a1) fzero a2<a1 = ≈fzero
<→fcross≈id {suc m} (fsuc a1) (fsuc a2) (<fsuc a2<a1) =
  ≈fsuc (<→fcross≈id a1 a2 a2<a1)

≈→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≈ᶠ a1 → fcross a1 a2 ≈ᶠ a2
≈→fcross≈id fzero fzero _ = ≈fzero
≈→fcross≈id (fsuc a1) fzero _ = ≈fzero
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

fin-restrict-<-a≈a
  : ∀ {x} {b : Fin (suc x)} (a : Fin y)
  → (a<b : a <ᶠ b) → fin-restrict-< a a<b ≈ᶠ a
fin-restrict-<-a≈a {x = suc x} fzero <fzero = ≈fzero
fin-restrict-<-a≈a {x = suc x} (fsuc a) (<fsuc a<b) =
  ≈fsuc (fin-restrict-<-a≈a a a<b)

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

fcross0≡0 : ∀ {m} → (a : Fin (suc m))
          → fcross a fzero ≡ fzero
fcross0≡0 fzero = refl
fcross0≡0 (fsuc a) = refl

fcross0s≡pred : ∀ {m} → (a : Fin (suc m))
              → fcross f0 (fsuc a) ≡ a
fcross0s≡pred a = refl

fcross-fcross-fsplice
  : ∀ {m} → (b : Fin (suc (suc m))) (c : Fin (suc m))
  → (fcross (fcross c b) (fsplice b c)) ≡ c
fcross-fcross-fsplice fzero fzero = refl
fcross-fcross-fsplice fzero (fsuc c) = refl
fcross-fcross-fsplice (fsuc b) fzero = fcross0≡0 b
fcross-fcross-fsplice {m = suc m} (fsuc b) (fsuc c) =
  cong fsuc (fcross-fcross-fsplice b c)

finject-+ : ∀ (x y z : ℕ) → (a : Fin x)
          → finject z (finject y a)
          ≡ subst Fin (ℕ.+-assoc x y z) (finject (y ℕ.+ z) a)
finject-+ (suc x) zero z fzero =
  finject z (finject zero fzero)
    ≡⟨ refl ⟩
  finject z fzero 
    ≡⟨ refl ⟩
  fzero 
    ≡⟨ fzero≡subst-fzero (ℕ.+-assoc x zero z) ⟩
  subst Fin (ℕ.+-assoc (suc x) zero z) fzero 
    ≡⟨ refl ⟩
  subst Fin (ℕ.+-assoc (suc x) zero z) (finject (zero +ℕ z) fzero) ▯
finject-+ (suc x) zero z (fsuc a) =
  finject z (finject zero (fsuc a))
    ≡⟨ refl ⟩
  finject z (fsuc (finject zero a))
    ≡⟨ refl ⟩
  fsuc (finject z (finject zero a))
    ≡⟨ cong fsuc (finject-+ x 0 z a) ⟩
  fsuc (subst Fin (ℕ.+-assoc x zero z) (finject (zero +ℕ z) a))
    ≡⟨ sym (subst-fsuc-reorder (ℕ.+-assoc x zero z) (finject (zero +ℕ z) a)) ⟩
  subst Fin (ℕ.+-assoc (suc x) zero z) (fsuc (finject (zero +ℕ z) a))
    ≡⟨ refl ⟩
  subst Fin (ℕ.+-assoc (suc x) zero z) (finject (zero +ℕ z) (fsuc a)) ▯
finject-+ (suc x) (suc y) z fzero =
  finject z (finject (suc y) fzero)
    ≡⟨ refl ⟩
  finject z fzero
    ≡⟨ refl ⟩
  fzero
    ≡⟨ fzero≡subst-fzero (ℕ.+-assoc x (suc y) z) ⟩
  subst Fin (ℕ.+-assoc (suc x) (suc y) z) fzero
    ≡⟨ refl ⟩
  subst Fin (ℕ.+-assoc (suc x) (suc y) z) (finject (suc y +ℕ z) fzero) ▯ 
finject-+ (suc x) (suc y) z (fsuc a) =
  finject z (finject (suc y) (fsuc a))
    ≡⟨ refl ⟩
  finject z (fsuc (finject (suc y) a))
    ≡⟨ refl ⟩
  fsuc (finject z (finject (suc y) a))
    ≡⟨ cong fsuc (finject-+ x (suc y) z a)  ⟩
  fsuc (subst Fin (ℕ.+-assoc x (suc y) z) (finject (suc y +ℕ z) a))
    ≡⟨ sym (subst-fsuc-reorder (ℕ.+-assoc x (suc y) z) (finject (suc y +ℕ z) a)) ⟩
  subst Fin (ℕ.+-assoc (suc x) (suc y) z) (fsuc (finject (suc y +ℕ z) a))
    ≡⟨ refl ⟩
  subst Fin (ℕ.+-assoc (suc x) (suc y) z) (finject (suc y +ℕ z) (fsuc a)) ▯


subst0≡fcast0 : {x y : ℕ} (p : x ≡ y)
              → subst (Fin ∘ suc) p (fzero {x}) ≡ fcast (cong suc p) (fzero {x})
subst0≡fcast0 p = sym (fzero≡subst-fzero p)

subst≡fcast : ∀ {x y : ℕ} (p : x ≡ y) (a : Fin x)
            → subst Fin p a ≡ fcast p a 
subst≡fcast {suc x} {zero} p a = absurd (ℕ.snotz p)
subst≡fcast {suc x} {suc y} p fzero =
  subst (λ ○ → subst Fin ○ f0 ≡ fcast ○ f0) (path-suc-pred p) base
  where
    x≡y : x ≡ y
    x≡y = cong ℕ.predℕ p
    base : subst Fin (cong suc x≡y) f0 ≡ fcast (cong suc x≡y) f0
    base = subst0≡fcast0 {x = x} {y = y} x≡y
subst≡fcast {suc x} {suc y} p (fsuc a) =
  subst Fin p (fsuc a)
    ≡⟨ cong (λ ○ → subst Fin ○ (fsuc a)) (sym (path-suc-pred p)) ⟩
  subst Fin (cong suc q) (fsuc a)
    ≡⟨ subst-fsuc-reorder (cong ℕ.predℕ p) a ⟩
  fsuc (subst Fin q a)
    ≡⟨ cong fsuc (subst≡fcast q a) ⟩
  fsuc (fcast q a)
    ≡⟨ refl ⟩
  fcast (cong suc q) (fsuc a)
    ≡⟨ refl ⟩
  fcast p (fsuc a) ▯ 
  where
    q : x ≡ y
    q = ℕ.injSuc p

fsplice-fcross-fcross-fsplice
  : {n : ℕ} → (b : Fin (suc (suc n))) (c : Fin (suc n)) (d : Fin n)
  → fsplice (fcross (fsplice c d) b) (fcross d c)
  ≡ (fcross (fsplice (fcross c b) d) (fsplice b c))
fsplice-fcross-fcross-fsplice fzero fzero d = refl
fsplice-fcross-fcross-fsplice fzero (fsuc c) fzero = refl
fsplice-fcross-fcross-fsplice fzero (fsuc c) (fsuc d) = refl
fsplice-fcross-fcross-fsplice (fsuc b) fzero fzero = sym (fcross0≡0 (fsplice b f0))
fsplice-fcross-fcross-fsplice (fsuc b) fzero (fsuc d) = sym (fcross0≡0 (fsplice b (fsuc d)))
fsplice-fcross-fcross-fsplice (fsuc b) (fsuc c) fzero = refl
fsplice-fcross-fcross-fsplice (fsuc b) (fsuc c) (fsuc d) =
  cong fsuc (fsplice-fcross-fcross-fsplice b c d)

fcross-fcross-fcross-fsplice
  : {n : ℕ} → (b : Fin (suc (suc n))) (c : Fin (suc n)) (d : Fin n)
  → fcross (fcross d c) (fcross (fsplice c d) b)
  ≡ fcross d (fcross c b)
fcross-fcross-fcross-fsplice fzero fzero fzero = refl
fcross-fcross-fcross-fsplice fzero fzero (fsuc d) = refl
fcross-fcross-fcross-fsplice fzero (fsuc c) fzero = fcross0≡0 c
fcross-fcross-fcross-fsplice fzero (fsuc c) (fsuc d) = refl
fcross-fcross-fcross-fsplice (fsuc b) fzero fzero = refl
fcross-fcross-fcross-fsplice (fsuc b) fzero (fsuc d) = refl
fcross-fcross-fcross-fsplice (fsuc b) (fsuc c) fzero = refl
fcross-fcross-fcross-fsplice (fsuc b) (fsuc c) (fsuc d) =
  cong fsuc (fcross-fcross-fcross-fsplice b c d)

open _∖_

module DelZeroSuc {x : ℕ} (b :  ⟦ x ⟧) where
  B : (suc x ∖ fzero)
  B = fsuc b — fzero≢fsuc {i = b}

  del-zero-suc : del fzero B ≡ b
  del-zero-suc with (del fzero B) | inspect (del fzero) B
  ... | fzero | [ p ]ᵢ = sym p
  ... | fsuc A | [ p ]ᵢ = sym p

open DelZeroSuc using (del-zero-suc)

del-suc-zero : ∀ {x} (a : ⟦ suc x ⟧)
             → del (fsuc a) (fzero — fsuc≢fzero {i = a}) ≡ fzero
del-suc-zero a = refl

del-suc-suc : ∀ {x} (a b : ⟦ suc x ⟧) → (a'≢b' : fsuc a ≢ fsuc b)
             → del (fsuc a) (fsuc b — a'≢b')
             ≡ fsuc (del a (b — ≢cong fsuc a'≢b'))
del-suc-suc {zero} fzero fzero a'≢b' =
  absurd (a'≢b' refl)
del-suc-suc {suc x} a b a'≢b' = refl

del-inj : {x : ℕ} → (a : ⟦ suc x ⟧)
        → (B C : (suc x ∖ a))
        → del a B ≡ del a C
        → val B ≡ val C
del-inj {x = zero} fzero (fzero — a≢b) _ _ =
  absurd (a≢b refl)
del-inj {x = suc x} fzero (fzero — a≢b) _ _ =
  absurd (a≢b refl)
del-inj {x = suc x} fzero (fsuc _ — _) (fzero — a≢c) _ =
  absurd (a≢c refl)
del-inj {x = suc x} fzero (fsuc b — a≢b) (fsuc c — a≢c) b'≡c' =
  cong fsuc b'≡c'
del-inj {x = suc x} (fsuc a) (fzero — a≢b) (fzero — a≢c) b'≡c' =
  refl
del-inj {x = suc x} (fsuc a) (fzero — a≢b) (fsuc c — a≢c) b'≡c' =
  absurd (fzero≢fsuc b'≡c')
del-inj {x = suc x} (fsuc a) (fsuc b — a≢b) (fzero — a≢c) b'≡c'
  = absurd (fsuc≢fzero b'≡c')
del-inj {x = suc x} (fsuc a) (fsuc b — a≢b) (fsuc c — a≢c) b'≡c' = {!!}

ins-inj : {x : ℕ} → (a : ⟦ suc x ⟧)
        → (b c : Fin x)
        → val (ins a b) ≡ val (ins a c)
        → b ≡ c
ins-inj {x = zero} a b c a+b≡a+c = absurd (Fin0-absurd b)
ins-inj {x = suc x} a b c a+b≡a+c with a | b | c
... | fzero | fzero | fzero = refl
... | fzero | fzero | fsuc c' = absurd (fzero≢fsuc (fsuc-injective a+b≡a+c))
... | fzero | fsuc b' | fzero = absurd (fsuc≢fzero (fsuc-injective a+b≡a+c))
... | fzero | fsuc b' | fsuc c' = fsuc-injective a+b≡a+c
... | fsuc a' | fzero | fzero = refl
... | fsuc a' | fzero | fsuc c' = absurd (fzero≢fsuc a+b≡a+c)
... | fsuc a' | fsuc b' | fzero = absurd (fsuc≢fzero a+b≡a+c)
... | fsuc a' | fsuc b' | fsuc c' =
  cong fsuc (ins-inj a' b' c' (fsuc-injective a+b≡a+c))

fjoin≡fcross : {n : ℕ} → (a : Fin n) (b : Fin (suc n)) → (b≉a : b ≉ᶠ finj a)
             → fjoin (finj a) b b≉a ≡ fcross a b
fjoin≡fcross fzero fzero 0≉0 = absurd (0≉0 ≈refl)
fjoin≡fcross fzero (fsuc b) b'≉0 =
  fjoin (finj f0) (fsuc b) b'≉0
    ≡⟨ refl ⟩
  fjoin-cases (finj f0) (fsuc b) b'≉0 (fsuc b ≟ᶠ finj f0)
    ≡⟨ refl ⟩
  fjoin-cases (finj f0) (fsuc b) b'≉0 (fgt <fzero)
    ≡⟨ refl ⟩
  b
    ≡⟨ refl ⟩
  fcross f0 (fsuc b) ▯
fjoin≡fcross (fsuc a) fzero b≉a = refl
fjoin≡fcross (fsuc a) (fsuc b) b'≉a' =
  fjoin (finj (fsuc a)) (fsuc b) b'≉a'
    ≡⟨ fjoin-irrelevant (fsuc (finj a)) (fsuc b) b'≉a' (≉fsuc (≉fpred b'≉a')) ⟩
  fjoin (fsuc (finj a)) (fsuc b) (≉fsuc (≉fpred b'≉a'))
    ≡⟨ fsuc-fjoin (finj a) b (≉fpred b'≉a') ⟩
  fsuc (fjoin (finj a) b (≉fpred b'≉a'))
    ≡⟨ cong fsuc (fjoin≡fcross a b (≉fpred b'≉a')) ⟩
  fsuc (fcross a b)
    ≡⟨ refl ⟩
  fcross (fsuc a) (fsuc b) ▯

fjoin-isInjective : {n : ℕ} → (a b c : Fin (suc n)) → (b≉a : b ≉ᶠ a) → (c≉a : c ≉ᶠ a)
                  → fjoin a b b≉a ≡ fjoin a c c≉a → b ≡ c
fjoin-isInjective fzero fzero c 0≉0 c≉0 q = absurd (0≉0 ≈refl)
fjoin-isInjective fzero (fsuc b) fzero b'≉0 0≉0 q = absurd (0≉0 ≈refl)
fjoin-isInjective {suc n} fzero (fsuc b) (fsuc c) b'≉a c'≉a q =
  cong fsuc p
  where p : b ≡ c
        p = b
              ≡⟨ sym (fjoin≡fcross f0 (fsuc b) b'≉a) ⟩
            fjoin f0 (fsuc b) b'≉a
              ≡⟨ q ⟩
            fjoin f0 (fsuc c) c'≉a
              ≡⟨ fjoin≡fcross f0 (fsuc c) c'≉a ⟩
            c ▯
fjoin-isInjective (fsuc a) fzero fzero 0≉a' _ q = refl
fjoin-isInjective {suc n} (fsuc a) fzero (fsuc c) 0≉a' c'≉a' q
  with (fsuc c) ≟ᶠ (fsuc a)
... | flt (<fsuc c<a) = ≈ᶠ→≡ $ ≈ᶠ-trans ≈fzero $ ≈ᶠ-trans (≡→≈ᶠ q)
                      $ ≈fsuc (fin-restrict-<-a≈a c c<a)
... | feq (≈fsuc c≈a) = absurd (c'≉a' (≈fsuc c≈a))
fjoin-isInjective {suc n} (fsuc a) fzero (fsuc (fsuc c)) 0≉a' c'≉a' q
    | fgt (<fsuc c>a) = absurd (fzero≢fsuc q)
fjoin-isInjective {suc n} (fsuc a) (fsuc b) fzero b'≉a' 0≉a' q
  with (fsuc b) ≟ᶠ (fsuc a)
... | flt (<fsuc b<a) = sym $ ≈ᶠ→≡ $ ≈ᶠ-trans ≈fzero $ ≈ᶠ-trans (≡→≈ᶠ (sym q))
                      $ ≈fsuc (fin-restrict-<-a≈a b b<a)
... | feq (≈fsuc b≈a) = absurd (b'≉a' (≈fsuc b≈a))
fjoin-isInjective {suc n} (fsuc a) (fsuc (fsuc b)) fzero b'≉a' 0≉a' q
    | fgt (<fsuc b>a) = absurd (fzero≢fsuc (sym q))
fjoin-isInjective {n = suc n} (fsuc a) (fsuc b) (fsuc c) b≉a c≉a q =
  cong fsuc (fjoin-isInjective a b c (≉fpred b≉a) (≉fpred c≉a) r)
  where
    r : fjoin a b (≉fpred b≉a) ≡ fjoin a c (≉fpred c≉a)
    r = fsuc-injective (
      fsuc (fjoin a b (≉fpred b≉a))
        ≡⟨ sym (fsuc-fjoin a b (≉fpred b≉a)) ⟩
      fjoin (fsuc a) (fsuc b) (≉fsuc (≉fpred b≉a))
        ≡⟨ fjoin-irrelevant (fsuc a) (fsuc b) (≉fsuc (≉fpred b≉a)) b≉a ⟩
      fjoin (fsuc a) (fsuc b) b≉a
        ≡⟨ q ⟩
      fjoin (fsuc a) (fsuc c) c≉a
        ≡⟨ fjoin-irrelevant (fsuc a) (fsuc c) c≉a (≉fsuc (≉fpred c≉a)) ⟩
      fjoin (fsuc a) (fsuc c) (≉fsuc (≉fpred c≉a))
        ≡⟨ fsuc-fjoin a c (≉fpred c≉a) ⟩
      fsuc (fjoin a c (≉fpred c≉a)) ▯)
