module VSet.Data.Fin.Order where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order
open import VSet.Data.Fin.Base

open ℕ.ℕ

private
  variable
    ℓ : Level
    x y z : ℕ
    a : Fin x
    b : Fin y
    c : Fin z

data _<ᶠ_ : {x y : ℕ} (a : Fin x) → (b : Fin y) → Type where
  <fzero : {b : Fin y} → (fzero {x}) <ᶠ fsuc b
  <fsuc : {a : Fin x} {b : Fin y} → a <ᶠ b → fsuc a <ᶠ fsuc b

data _≈ᶠ_ : {x y : ℕ} (a : Fin x) → (b : Fin y) → Type where
  ≈fzero : (fzero {x}) ≈ᶠ (fzero {y})
  ≈fsuc : {a : Fin x} {b : Fin y} → a ≈ᶠ b → fsuc a ≈ᶠ fsuc b

_≉ᶠ_ : Fin x → Fin y → Type
a ≉ᶠ b = ¬ a ≈ᶠ b

≈fsym : a ≈ᶠ b → b ≈ᶠ a
≈fsym ≈fzero = ≈fzero
≈fsym (≈fsuc a≈b) = ≈fsuc (≈fsym a≈b)

≉fsym : a ≉ᶠ b → b ≉ᶠ a
≉fsym a≉b b≈a = a≉b (≈fsym b≈a)

≈refl : a ≈ᶠ a
≈refl {a = fzero} = ≈fzero
≈refl {a = fsuc a} = ≈fsuc (≈refl {a = a})

≡→≈ᶠ : {a b : Fin x} → a ≡ b → a ≈ᶠ b 
≡→≈ᶠ {a = a} a≡b = subst (a ≈ᶠ_) a≡b ≈refl

≈ᶠ→≡ : {a b : Fin x} → a ≈ᶠ b → a ≡ b
≈ᶠ→≡ ≈fzero = refl
≈ᶠ→≡ (≈fsuc a≈b) = cong fsuc (≈ᶠ→≡ a≈b)

fzero≉fsuc : fzero {x} ≉ᶠ fsuc b
fzero≉fsuc ()

fsuc≉fzero : fsuc a ≉ᶠ fzero {y}
fsuc≉fzero ()

≈fsuc-injective : fsuc a ≈ᶠ fsuc b → a ≈ᶠ b
≈fsuc-injective (≈fsuc a≈b) = a≈b

_≤ᶠ_ : (a : Fin x) (b : Fin y) → Type
_≤ᶠ_ {x = x} {y = y} a b = (a <ᶠ b) ⊎ (a ≈ᶠ b)


data Trichotomyᶠ {x y} (a : Fin x) (b : Fin y) : Type where
  flt : a <ᶠ b → Trichotomyᶠ a b
  feq : a ≈ᶠ b → Trichotomyᶠ a b
  fgt : b <ᶠ a → Trichotomyᶠ a b

open Trichotomyᶠ

data Bichotomyᶠ {x y} (a : Fin x) (b : Fin y) : Type where
  fle : a ≤ᶠ b → Bichotomyᶠ a b
  fgt : b <ᶠ a → Bichotomyᶠ a b

open Bichotomyᶠ

_≟ᶠ-suc_ : ∀ {x} → (a : Fin x) (b : Fin y)
          → Trichotomyᶠ a b → Trichotomyᶠ (fsuc a) (fsuc b) 
(a ≟ᶠ-suc b) (flt a<b) = flt (<fsuc a<b)
(a ≟ᶠ-suc b) (feq a≈b) = feq (≈fsuc a≈b)
(a ≟ᶠ-suc b) (fgt b<a) = fgt (<fsuc b<a)

_≟ᶠ_ : ∀ (a : Fin x) (b : Fin y) → Trichotomyᶠ a b 
fzero ≟ᶠ fzero = feq (≈fzero)
fzero ≟ᶠ fsuc b = flt <fzero
fsuc a ≟ᶠ fzero = fgt <fzero
fsuc a ≟ᶠ fsuc b = (a ≟ᶠ-suc b) (a ≟ᶠ b)

Trichotomy→Bichotomyᶠ
  : ∀ {x} {a : Fin x} {b : Fin y}
  → Trichotomyᶠ a b → Bichotomyᶠ a b 
Trichotomy→Bichotomyᶠ (flt a<b) = fle (inl a<b)
Trichotomy→Bichotomyᶠ (feq a≈b) = fle (inr a≈b)
Trichotomy→Bichotomyᶠ (fgt b<a) = fgt b<a

_≤?ᶠ_ : (a : Fin x) (b : Fin y) → Bichotomyᶠ a b 
a ≤?ᶠ b = Trichotomy→Bichotomyᶠ (a ≟ᶠ b)

fsuc∘pred≡id : a ≉ᶠ fzero {y} → fsuc (pred a) ≡ a
fsuc∘pred≡id {a = fzero} 0≉0 = absurd (0≉0 ≈fzero)
fsuc∘pred≡id {a = fsuc a} a'≉0 = refl

<ᶠ-respects-pred : {a : Fin x} {b : Fin y} → fsuc a <ᶠ fsuc b → a <ᶠ b
<ᶠ-respects-pred (<fsuc a'<b') = a'<b'

≤ᶠ-respects-pred : {a : Fin x} {b : Fin y} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤ᶠ-respects-pred (inl a'<b') = inl (<ᶠ-respects-pred a'<b')
≤ᶠ-respects-pred (inr a'≈b') = inr (≈fsuc-injective a'≈b')

≤ᶠ-respects-fsuc : {a : Fin x} {b : Fin y} → a ≤ᶠ b → fsuc a ≤ᶠ fsuc b 
≤ᶠ-respects-fsuc (inl a<b) = inl (<fsuc a<b)
≤ᶠ-respects-fsuc (inr a≈b) = inr (≈fsuc a≈b)

fzero≤a : ∀ {x : ℕ} → (a : Fin (suc x)) → fzero {y} ≤ᶠ a
fzero≤a fzero = inr ≈fzero
fzero≤a (fsuc a) = inl <fzero

weaken<-pred : ∀ {x} {a : Fin (suc x)} {b : Fin x}
             → a <ᶠ fsuc b → a ≤ᶠ finj b 
weaken<-pred {a = a} {b = b} <fzero = fzero≤a (finj b)
weaken<-pred {a = fsuc a} {b = fsuc b} (<fsuc a<b) =
  ≤ᶠ-respects-fsuc (weaken<-pred a<b)

≈ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a ≈ᶠ b → b ≈ᶠ c → a ≈ᶠ c
≈ᶠ-trans ≈fzero ≈fzero = ≈fzero
≈ᶠ-trans (≈fsuc a≈b) (≈fsuc b≈c) = ≈fsuc (≈ᶠ-trans a≈b b≈c)

<ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a <ᶠ b → b <ᶠ c → a <ᶠ c
<ᶠ-trans <fzero (<fsuc b<c) = <fzero
<ᶠ-trans (<fsuc a<b) (<fsuc b<c) = <fsuc (<ᶠ-trans a<b b<c)

<≤ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a <ᶠ b → b ≤ᶠ c → a <ᶠ c
<≤ᶠ-trans a<b (inl b<c) = <ᶠ-trans a<b b<c
<≤ᶠ-trans <fzero (inr (≈fsuc b≈c)) = <fzero
<≤ᶠ-trans (<fsuc a<b) (inr (≈fsuc b≈c)) = <fsuc (<≤ᶠ-trans a<b (inr b≈c))

≤<ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a ≤ᶠ b → b <ᶠ c → a <ᶠ c
≤<ᶠ-trans (inl a<b) b<c = <ᶠ-trans a<b b<c
≤<ᶠ-trans (inr ≈fzero) <fzero = <fzero
≤<ᶠ-trans (inr (≈fsuc a≈b)) (<fsuc b<c) = <fsuc (≤<ᶠ-trans (inr a≈b) b<c)

≤ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a ≤ᶠ b → b ≤ᶠ c → a ≤ᶠ c
≤ᶠ-trans (inl a<b) (inl b<c) = inl (<ᶠ-trans a<b b<c)
≤ᶠ-trans (inl a<b) (inr b≈c) = inl (<≤ᶠ-trans a<b (inr b≈c))
≤ᶠ-trans (inr a≈b) (inl b<c) = inl (≤<ᶠ-trans (inr a≈b) b<c)
≤ᶠ-trans (inr a≈b) (inr b≈c) = inr (≈ᶠ-trans a≈b b≈c)

<-suc : ∀ (a : Fin x) → a <ᶠ fsuc a 
<-suc fzero = <fzero
<-suc (fsuc a) = <fsuc (<-suc a)

≤-pred : ∀ {a : Fin x} {b : Fin y} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤-pred (inl (<fsuc a<b)) = inl a<b
≤-pred (inr (≈fsuc a≈b)) = inr a≈b

fsuc≤fsuc : a ≤ᶠ b → fsuc a ≤ᶠ fsuc b
fsuc≤fsuc (inl a<b) = inl (<fsuc a<b)
fsuc≤fsuc (inr a≈b) = inr (≈fsuc a≈b)

≤ᶠ→<ᶠ : {a : Fin x} {b : Fin y} → a ≤ᶠ b → a <ᶠ fsuc b
≤ᶠ→<ᶠ {b = b} (inl a<b) = <ᶠ-trans a<b (<-suc b) 
≤ᶠ→<ᶠ (inr ≈fzero) = <fzero
≤ᶠ→<ᶠ (inr (≈fsuc a≈b)) = <fsuc (≤ᶠ→<ᶠ (inr a≈b))

<ᶠ→≤ᶠ : {a : Fin x} {b : Fin y} → a <ᶠ fsuc b → a ≤ᶠ b
<ᶠ→≤ᶠ {a = fzero} {fzero} a<b' = inr ≈fzero
<ᶠ→≤ᶠ {a = fzero} {fsuc b} 0<b' = inl <fzero
<ᶠ→≤ᶠ {a = fsuc a} {fsuc b} (<fsuc a<b) = fsuc≤fsuc (<ᶠ→≤ᶠ a<b)

¬a<a : {a : Fin x} → ¬ a <ᶠ a
¬a<a {a = fsuc a} (<fsuc a<a) = ¬a<a a<a

≉ᶠ→≢ : {a b : Fin x} → a ≉ᶠ b → a ≢ b
≉ᶠ→≢ a≉b a≡b = a≉b (≡→≈ᶠ a≡b)


<ᶠ→≉ : {a : Fin x} {b : Fin y} → a <ᶠ b → a ≉ᶠ b
<ᶠ→≉ {a = fzero} {b = fsuc b} <fzero a≈b = fzero≉fsuc a≈b
<ᶠ→≉ {a = fsuc a} {b = fsuc b} (<fsuc a<b) a≈b =
  <ᶠ→≉ {a = a} {b = b} a<b (≈fsuc-injective a≈b)

<ᶠ→≢ : {a b : Fin x} → a <ᶠ b → a ≢ b
<ᶠ→≢ a<b = ≉ᶠ→≢ (<ᶠ→≉ a<b)

≤ᶠ→≯ᶠ : {a : Fin x} {b : Fin y} → a ≤ᶠ b → ¬ b <ᶠ a
≤ᶠ→≯ᶠ (inl (<fsuc a<b)) (<fsuc a>b) = ≤ᶠ→≯ᶠ (inl a<b) a>b
≤ᶠ→≯ᶠ (inr a≈b) a>b = <ᶠ→≉ a>b (≈fsym a≈b)

<ᶠ→≯ᶠ : {a : Fin x} {b : Fin y} → a <ᶠ b → ¬ b <ᶠ a
<ᶠ→≯ᶠ a<b b<a = ¬a<a  (<ᶠ-trans a<b b<a)

fsuc≤fsuc→<fsuc : (a≤b : a ≤ᶠ b) → ≤ᶠ→<ᶠ (fsuc≤fsuc a≤b) ≡ <fsuc (≤ᶠ→<ᶠ a≤b)
fsuc≤fsuc→<fsuc (inl x) = refl
fsuc≤fsuc→<fsuc (inr x) = refl

fin-restrict-< : ∀ {x} {b : Fin (suc x)} (a : Fin y)
               → a <ᶠ b → Fin x
fin-restrict-< {x = suc x} fzero <fzero = fzero
fin-restrict-< {x = suc x} (fsuc a) (<fsuc a<b) = fsuc (fin-restrict-< a a<b)

fin-restrict-≤ : ∀ {x} {b : Fin x} (a : Fin y)
               → a ≤ᶠ b → Fin x
fin-restrict-≤ a a≤b = fin-restrict-< a (≤ᶠ→<ᶠ a≤b)

fin-restrict-<≡fin-restrict-≤ 
  : ∀ {x} {y} → {b : Fin x} (a : Fin y) → (a≤b : a ≤ᶠ b)
  → fin-restrict-< a (≤ᶠ→<ᶠ a≤b) ≡ fin-restrict-≤ a a≤b
fin-restrict-<≡fin-restrict-≤ a a≤b =
  refl

fin-restrict' : ∀ {x} {b : Fin x} (a : Fin (suc x))
              → a ≤ᶠ b → Fin x
fin-restrict' {x = 0} {b} a x = b
fin-restrict' {x = suc x} {b = fsuc b} fzero (inl 0<b') = fzero
fin-restrict' {x = suc x} fzero (inr 0≈b) = fzero
fin-restrict' {x = suc x} {b = fsuc b} (fsuc a) (inl (<fsuc a<b)) = fsuc (fin-restrict' a (inl a<b))
fin-restrict' {x = suc x} {b = fzero} (fsuc a) (inr a'≈0) = absurd (fsuc≉fzero a'≈0)
fin-restrict' {x = suc x} {b = fsuc b} (fsuc a) (inr a'≈b') = fsuc (fin-restrict' a (inr (≈fsuc-injective a'≈b')))

case≤?ᶠ : {A : Type} {m : ℕ} (a b : Fin m) → A → A → A
case≤?ᶠ a b x y = case (a ≤?ᶠ b) of
  λ{ (fle _) → x
   ; (fgt _) → y }

≤?ᶠ-suc : {a : Fin x} {b : Fin y} → Bichotomyᶠ a b → Bichotomyᶠ (fsuc a) (fsuc b)  
≤?ᶠ-suc (fle a≤b) = fle (fsuc≤fsuc a≤b)
≤?ᶠ-suc (fgt a>b) = fgt (<fsuc a>b)

isProp≈ᶠ : {a : Fin x} {b : Fin y} → isProp (a ≈ᶠ b)
isProp≈ᶠ ≈fzero ≈fzero = refl
isProp≈ᶠ (≈fsuc u) (≈fsuc v) = cong ≈fsuc (isProp≈ᶠ u v)

isProp<ᶠ : {a : Fin x} {b : Fin y} → isProp (a <ᶠ b)
isProp<ᶠ <fzero <fzero = refl
isProp<ᶠ (<fsuc u) (<fsuc v) = cong <fsuc (isProp<ᶠ u v)

isProp≤ᶠ : {a : Fin x} {b : Fin y} → isProp (a ≤ᶠ b)
isProp≤ᶠ (inl u) (inl v) = cong inl (isProp<ᶠ u v)
isProp≤ᶠ (inl u) (inr v) = absurd (<ᶠ→≉ u v)
isProp≤ᶠ (inr u) (inl v) = absurd (<ᶠ→≉ v u)
isProp≤ᶠ (inr u) (inr v) = cong inr (isProp≈ᶠ u v)

isPropBichotomyᶠ : {a : Fin x} {b : Fin y} → isProp (Bichotomyᶠ a b)
isPropBichotomyᶠ (fle u) (fle v) = cong fle (isProp≤ᶠ u v)
isPropBichotomyᶠ (fle u) (fgt v) = absurd (≤ᶠ→≯ᶠ u v)
isPropBichotomyᶠ (fgt u) (fle v) = absurd (≤ᶠ→≯ᶠ v u)
isPropBichotomyᶠ (fgt u) (fgt v) = cong fgt (isProp<ᶠ u v)

isPropTrichotomyᶠ : {a : Fin x} {b : Fin y} → isProp (Trichotomyᶠ a b)
isPropTrichotomyᶠ (flt u) (flt v) = cong flt (isProp<ᶠ u v)
isPropTrichotomyᶠ (flt u) (feq v) = absurd (<ᶠ→≉ u v)
isPropTrichotomyᶠ (flt u) (fgt v) = absurd (<ᶠ→≯ᶠ u v)
isPropTrichotomyᶠ (feq u) (flt v) = absurd (<ᶠ→≉ v u)
isPropTrichotomyᶠ (feq u) (feq v) = cong feq (isProp≈ᶠ u v)
isPropTrichotomyᶠ (feq u) (fgt v) = absurd (<ᶠ→≉ v (≈fsym u))
isPropTrichotomyᶠ (fgt u) (flt v) = absurd (<ᶠ→≯ᶠ v u)
isPropTrichotomyᶠ (fgt u) (feq v) = absurd (<ᶠ→≉ u (≈fsym v))
isPropTrichotomyᶠ (fgt u) (fgt v) = cong fgt (isProp<ᶠ u v)

≤?ᶠ-pred : (a : Fin x) (b : Fin y) → fsuc a ≤?ᶠ fsuc b ≡ ≤?ᶠ-suc (a ≤?ᶠ b)
≤?ᶠ-pred a b with a ≟ᶠ b
... | flt a<b = refl
... | feq a≈b = refl
... | fgt a>b = refl

≈ᶠ-inj : ∀ (a : Fin x) → finj a ≈ᶠ a
≈ᶠ-inj fzero = ≈fzero
≈ᶠ-inj (fsuc a) = ≈fsuc (≈ᶠ-inj a)

≈ᶠ-inject : ∀ y → (a : Fin x) → finject y a ≈ᶠ a
≈ᶠ-inject y fzero = ≈fzero
≈ᶠ-inject zero (fsuc a) = ≈fsuc (≈ᶠ-inject 0 a)
≈ᶠ-inject (suc y) (fsuc a) = ≈fsuc (≈ᶠ-inject (suc y) a)

<ᶠ-respects-≈ᶠ : ∀ {w x y z : ℕ}
               → {a : Fin w} {b : Fin x} {c : Fin y} {d : Fin z}
               → a ≈ᶠ b → b <ᶠ c → c ≈ᶠ d → a <ᶠ d
<ᶠ-respects-≈ᶠ ≈fzero <fzero (≈fsuc c≈d) = <fzero
<ᶠ-respects-≈ᶠ (≈fsuc a≈b) (<fsuc b<c) (≈fsuc c≈d) =
  <fsuc (<ᶠ-respects-≈ᶠ a≈b b<c c≈d)

<ᶠ-inject : (x' y' : ℕ) (a : Fin x) (b : Fin y) → a <ᶠ b → finject x' a <ᶠ finject y' b 
<ᶠ-inject x' y' a b a<b =
  <ᶠ-respects-≈ᶠ (≈ᶠ-inject x' a) a<b (≈fsym (≈ᶠ-inject y' b))

<ᶠ-inj-l : {a : Fin x} {b : Fin y} → a <ᶠ b → finj a <ᶠ b 
<ᶠ-inj-l a<b =
  <ᶠ-respects-≈ᶠ (≈ᶠ-inj _) a<b (≈refl)
