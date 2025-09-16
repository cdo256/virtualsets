<!--
```
module Dissertation.Fin where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat as ℕ hiding (elim)
open import Cubical.Data.Nat using (ℕ; +-zero; +-suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Prelude
open import VSet.Data.Nat.Order
open import VSet.Data.Nat.Properties
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Path
open import VSet.Prelude

private
  variable
    ℓ : Level
    x y z : ℕ
```
-->

\begin{verbatim}[hide]
module DissertationTex.Fin where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat as ℕ hiding (elim)
open import Cubical.Data.Nat using (ℕ; +-zero; +-suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Prelude
open import VSet.Data.Nat.Order
open import VSet.Data.Nat.Properties
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Path
open import VSet.Prelude

private
  variable
    ℓ : Level
    x y z : ℕ
\end{verbatim}

```
open ℕ.ℕ
```

We choose to define our own definition of Fin, which is identical to
the one in the standard library (but not in the cubical library).
We also define an alias with semantic brackets which is used in our
definition of `InjFun`.

Unless otherwise stated, all definitions in this section originate
from the standard librar.
```
data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

⟦_⟧ : ℕ → Type
⟦_⟧ = Fin
```

Next we define some numerals, which will make it easier to construct
definitions of injective functions.
```
f0 : Fin (1 ℕ.+ x)
f0 = fzero
f1 : Fin (2 ℕ.+ x)
f1 = fsuc f0
f2 : Fin (3 ℕ.+ x)
f2 = fsuc f1
f3 : Fin (4 ℕ.+ x)
f3 = fsuc f2
f4 : Fin (5 ℕ.+ x)
f4 = fsuc f3
f5 : Fin (6 ℕ.+ x)
f5 = fsuc f4
f6 : Fin (7 ℕ.+ x)
f6 = fsuc f5
f7 : Fin (8 ℕ.+ x)
f7 = fsuc f6
f8 : Fin (9 ℕ.+ x)
f8 = fsuc f7
f9 : Fin (10 ℕ.+ x)
f9 = fsuc f8
```

We also use the `DISPLAY` pragma mainly for terser debugging. 
```
{-# DISPLAY fzero = f0 #-}
{-# DISPLAY fsuc fzero = f1 #-}
{-# DISPLAY fsuc (fsuc fzero) = f2 #-}
{-# DISPLAY fsuc (fsuc (fsuc fzero)) = f3 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc fzero))) = f4 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc fzero)))) = f5 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = f6 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = f7 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = f8 #-}
{-# DISPLAY fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = f9 #-}
```

Next we construct an eliminator for `Fin`, that is a function that
takes a map from all the ways to construct a `Fin`, and returns a
certain arbitrary type. It saves explicitly pattern matching, which
can be clearer in some cases.
```
elim : ∀ {A : {n : ℕ} → Fin (suc n) → Type }
     → ({n : ℕ} → A {n} fzero)
     → ({n : ℕ} → (a : Fin (suc n)) → A a → A (fsuc a))
     → ((m : ℕ) → (a : Fin (suc m)) → A a)
elim {A = A} z s m fzero = z
elim {A = A} z s (suc m) (fsuc a) = s a (elim {A = A} z s m a)
```

We define a predecessor function `pred` and a function `fmax` that
returns the largest element in `Fin (suc x)`.
```
pred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
pred fzero = fzero
pred (fsuc n) = n

fmax : ∀ {x} → Fin (suc x)
fmax {zero} = fzero
fmax {suc x} = fsuc (fmax {x})
```

Next we inductively define methods to go to and from `ℕ`. The first is
straight-forward, but the second requires a explicit proof that the
input value will fit within the `Fin` set.
```
toℕ : ∀ {n} → Fin n → ℕ 
toℕ fzero = zero
toℕ (fsuc x) = suc (toℕ x)
```

`fromℕ`, is considerably more complex as it requires adding an absurd case,
requiring the monotonicity of `predℕ`.
```
fromℕ : ∀ {n} → (a : ℕ) → (a < n) → Fin n
fromℕ {zero} a a<0 = absurd {A = Fin 0} (¬-<-zero {a} a<0)
fromℕ {suc n} zero _ = fzero
fromℕ {suc n} (suc a) sa<sn = fsuc (fromℕ {n} a (pred-<-pred {a} {n} sa<sn))
```

Next we define some operations on `Fin`. `fshift` and `finject` are
complementary functions that have ranges that don't overlap but do
cover the codomain. We will use this property when defining `⊎↔+`.
finj is a single step injection, which is useful because it can be
composed in certain cases to avoid having to `subst` across finite
indexes.
```
fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x +ℕ y)
fshift zero a = a
fshift (suc x) a = fsuc (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x +ℕ y)
finject {suc _} _ fzero = fzero
finject {suc x} y (fsuc a) = fsuc (finject {x} y a)

finj : {x : ℕ} → (a : Fin x) → Fin (suc x)
finj fzero = fzero
finj (fsuc a) = fsuc (finj a)
```

Next we turn to absurdities and negations. `fzero≢fsuc` and
`fsuc≢fzero` state the fact that we cannot have a value that is
constructed two distinct ways. This is a fact that is true for all
inductive types in general, but in Cubical Agda, an explicit transport
is required to demonstrate this. We transport the elemnt in `⊤`
(unit), into an element in `⊥` (empty) which is an absurdity as required.
```
fzero≢fsuc : ∀ {x : ℕ} {i : Fin x} → fzero ≢ fsuc i
fzero≢fsuc {x} p = transport (cong P p) tt
  where
    P : {x : ℕ} → Fin (suc x) → Type
    P {x} fzero = ⊤
    P {x} (fsuc a) = ⊥

fsuc≢fzero : ∀ {x : ℕ} {i : Fin x} → fsuc i ≢ fzero 
fsuc≢fzero = ≢sym fzero≢fsuc
```

Next we say that the empty `Fin` is equivalent to the canonical empty
type `⊥`.
```
Fin0≃⊥ : Fin 0 ≃ ⊥
Fin0≃⊥ = (λ ()) , record { equiv-proof = λ y → absurd y }

Fin0-absurd : {A : Type ℓ} → Fin 0 → A
Fin0-absurd ()
```

Next we prove that `fsuc` is an injective. This is another property of
inductive definitions: *There is only one way to construct an element
of an inductive type*.
```
fsuc-injective : ∀ {n} {i j : Fin n} → fsuc {n} i ≡ fsuc {n} j → i ≡ j
fsuc-injective {zero} {()} {()} 
fsuc-injective {suc n} {i} {j} p = cong pred p
```

Next we define a subtraction operator. This has the effect of removing a certain element from the domain of some `Fin`.

TODO: Remove this?

```
-- \setminus
record _∖_ (A : ℕ) (a : Fin A) : Type where
  constructor _—_
  field
    val : Fin A
    ne : a ≢ val
open _∖_
```

```
s_—0 : {A : ℕ} (a : Fin A) → suc A ∖ fzero 
s a —0 = fsuc a — fzero≢fsuc {i = a}
```

```
0—s_ : {A : ℕ} (a : Fin A) → suc A ∖ fsuc a
0—s a = fzero — fsuc≢fzero {i = a}
```

```
∖-suc : {A : ℕ} {a : Fin A} → A ∖ a → suc A ∖ fsuc a
∖-suc {suc A} (b — a≢b) = fsuc b — ≢cong pred a≢b
```

```
∖-pred : {A : ℕ} {a : Fin A} → (b : suc A ∖ fsuc a) → (val b ≢ fzero) → A ∖ a
∖-pred {suc A} (fzero — a≢b) 0≢0 = absurd (0≢0 refl)
∖-pred {suc A} (fsuc b — a≢b) _ = b — ≢cong fsuc a≢b
```

```
sa∖0≡a : {A : ℕ} → (a : suc A ∖ fzero) → ⟦ A ⟧
sa∖0≡a (fzero — 0≢0) = absurd (0≢0 refl)
sa∖0≡a (fsuc a — _) = a
```

```
ins : {x : ℕ} → (a : ⟦ suc x ⟧) → ⟦ x ⟧ → (suc x ∖ a)
ins {suc x} fzero b = fsuc b — fzero≢fsuc
ins {suc x} (fsuc a) fzero = fzero — fsuc≢fzero
ins {suc x} (fsuc a) (fsuc b) =
  fsuc c — λ sa≡sc →
    let a≡c = fsuc-injective {suc x} {a} {c} sa≡sc
    in ne (ins a b) a≡c
  where
    c = val (ins a b)
```

```
|Fin1|≡1 : (a b : ⟦ 1 ⟧) → a ≡ b
|Fin1|≡1 = isContr→isProp (fzero , f)
  where
    f : (y : ⟦ 1 ⟧) → fzero ≡ y
    f fzero = refl
```

```
del : {x : ℕ} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
del {ℕ.zero} fzero (fzero — 0≢0) = absurd (0≢0 refl)
del {suc x} fzero (fzero — 0≢0) = absurd (0≢0 refl)
del {suc x} fzero (fsuc b — a≢b) = b
del {suc x} (fsuc a) (fzero — a≢b) = fzero
del {suc x} (fsuc a) (fsuc b — a'≢b') =
  fsuc (del {x} a (b — ≢cong fsuc a'≢b'))
```

# Trichotomy on `Fin`

<!--
```
private
  variable
    a : Fin x
    b : Fin y
    c : Fin z
```
-->

\begin{verbatim}[hide]
private
  variable
    a : Fin x
    b : Fin y
    c : Fin z
\end{verbatim}


Next we define an order operator on Fin. My plan was to make a type
that is *propositional* for any two pairs of `Fin` using *trichotomy*,
which is a type with three constructors for `<`,`≡`, and `>`.

We desire an type `Trichotomyᶠ` with the following properties:

 1. We can compare two naturals and decide an order (greater, less or
 equal) between them.
 2. such a comparison is `propositional`,
 there the instance of the type is unique for that pair.
 3. It is decidable for any two pairs of `Fin`.
 4. It is heterongeneous: It can compare Fin with distinct types.

```
data _<ᶠ_ : {x y : ℕ} (a : Fin x) → (b : Fin y) → Type where
  <fzero : {b : Fin y} → (fzero {x}) <ᶠ fsuc b
  <fsuc : {a : Fin x} {b : Fin y} → a <ᶠ b → fsuc a <ᶠ fsuc b

data _≈ᶠ_ : {x y : ℕ} (a : Fin x) → (b : Fin y) → Type where
  ≈fzero : (fzero {x}) ≈ᶠ (fzero {y})
  ≈fsuc : {a : Fin x} {b : Fin y} → a ≈ᶠ b → fsuc a ≈ᶠ fsuc b
```

```
_≉ᶠ_ : Fin x → Fin y → Type
a ≉ᶠ b = ¬ a ≈ᶠ b
```

```
≈fsym : a ≈ᶠ b → b ≈ᶠ a
≈fsym ≈fzero = ≈fzero
≈fsym (≈fsuc a≈b) = ≈fsuc (≈fsym a≈b)
```

```
≉fsym : a ≉ᶠ b → b ≉ᶠ a
≉fsym a≉b b≈a = a≉b (≈fsym b≈a)
```

```
≈refl : a ≈ᶠ a
≈refl {a = fzero} = ≈fzero
≈refl {a = fsuc a} = ≈fsuc (≈refl {a = a})
```

```
≡→≈ᶠ : {a b : Fin x} → a ≡ b → a ≈ᶠ b 
≡→≈ᶠ {a = a} a≡b = subst (a ≈ᶠ_) a≡b ≈refl
```

```
≈ᶠ→≡ : {a b : Fin x} → a ≈ᶠ b → a ≡ b
≈ᶠ→≡ ≈fzero = refl
≈ᶠ→≡ (≈fsuc a≈b) = cong fsuc (≈ᶠ→≡ a≈b)
```

```
≢→≉ᶠ : {a b : Fin x} → a ≢ b → a ≉ᶠ b 
≢→≉ᶠ {a = a} a≢b a≈b = a≢b (≈ᶠ→≡ a≈b)
```

```
≉ᶠ→≢ : {a b : Fin x} → a ≉ᶠ b → a ≢ b
≉ᶠ→≢ a≉b a≡b = a≉b (≡→≈ᶠ a≡b)
```

```
fzero≉fsuc : fzero {x} ≉ᶠ fsuc b
fzero≉fsuc ()
```

```
fsuc≉fzero : fsuc a ≉ᶠ fzero {y}
fsuc≉fzero ()
```

```
≈fsuc-injective : fsuc a ≈ᶠ fsuc b → a ≈ᶠ b
≈fsuc-injective (≈fsuc a≈b) = a≈b
```

```
≉fpred : fsuc a ≉ᶠ fsuc b → a ≉ᶠ b
≉fpred a'≉b' a≈b = a'≉b' (≈fsuc a≈b)
```

```
_≤ᶠ_ : (a : Fin x) (b : Fin y) → Type
_≤ᶠ_ {x = x} {y = y} a b = (a <ᶠ b) ⊎ (a ≈ᶠ b)
```

```
data Trichotomyᶠ {x y} (a : Fin x) (b : Fin y) : Type where
  flt : a <ᶠ b → Trichotomyᶠ a b
  feq : a ≈ᶠ b → Trichotomyᶠ a b
  fgt : b <ᶠ a → Trichotomyᶠ a b
```

```
open Trichotomyᶠ
```

```
data Bichotomyᶠ {x y} (a : Fin x) (b : Fin y) : Type where
  fle : a ≤ᶠ b → Bichotomyᶠ a b
  fgt : b <ᶠ a → Bichotomyᶠ a b
```

```
open Bichotomyᶠ
```

```
_≟ᶠ-suc_ : ∀ {x} → (a : Fin x) (b : Fin y)
          → Trichotomyᶠ a b → Trichotomyᶠ (fsuc a) (fsuc b) 
(a ≟ᶠ-suc b) (flt a<b) = flt (<fsuc a<b)
(a ≟ᶠ-suc b) (feq a≈b) = feq (≈fsuc a≈b)
(a ≟ᶠ-suc b) (fgt b<a) = fgt (<fsuc b<a)
```

```
_≟ᶠ_ : ∀ (a : Fin x) (b : Fin y) → Trichotomyᶠ a b 
fzero ≟ᶠ fzero = feq (≈fzero)
fzero ≟ᶠ fsuc b = flt <fzero
fsuc a ≟ᶠ fzero = fgt <fzero
fsuc a ≟ᶠ fsuc b = (a ≟ᶠ-suc b) (a ≟ᶠ b)
```

```
Trichotomy→Bichotomyᶠ
  : ∀ {x} {a : Fin x} {b : Fin y}
  → Trichotomyᶠ a b → Bichotomyᶠ a b 
Trichotomy→Bichotomyᶠ (flt a<b) = fle (inl a<b)
Trichotomy→Bichotomyᶠ (feq a≈b) = fle (inr a≈b)
Trichotomy→Bichotomyᶠ (fgt b<a) = fgt b<a
```

```
_≤?ᶠ_ : (a : Fin x) (b : Fin y) → Bichotomyᶠ a b 
a ≤?ᶠ b = Trichotomy→Bichotomyᶠ (a ≟ᶠ b)
```

```
fsuc∘pred≡id : a ≉ᶠ fzero {y} → fsuc (pred a) ≡ a
fsuc∘pred≡id {a = fzero} 0≉0 = absurd (0≉0 ≈fzero)
fsuc∘pred≡id {a = fsuc a} a'≉0 = refl
```

```
<ᶠ-respects-pred : {a : Fin x} {b : Fin y} → fsuc a <ᶠ fsuc b → a <ᶠ b
<ᶠ-respects-pred (<fsuc a'<b') = a'<b'
```

```
≤ᶠ-respects-pred : {a : Fin x} {b : Fin y} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤ᶠ-respects-pred (inl a'<b') = inl (<ᶠ-respects-pred a'<b')
≤ᶠ-respects-pred (inr a'≈b') = inr (≈fsuc-injective a'≈b')
```

```
≤ᶠ-respects-fsuc : {a : Fin x} {b : Fin y} → a ≤ᶠ b → fsuc a ≤ᶠ fsuc b 
≤ᶠ-respects-fsuc (inl a<b) = inl (<fsuc a<b)
≤ᶠ-respects-fsuc (inr a≈b) = inr (≈fsuc a≈b)
```

```
fzero≤a : ∀ {x : ℕ} → (a : Fin (suc x)) → fzero {y} ≤ᶠ a
fzero≤a fzero = inr ≈fzero
fzero≤a (fsuc a) = inl <fzero
```

```
weaken<-pred : ∀ {x} {a : Fin (suc x)} {b : Fin x}
             → a <ᶠ fsuc b → a ≤ᶠ finj b 
weaken<-pred {a = a} {b = b} <fzero = fzero≤a (finj b)
weaken<-pred {a = fsuc a} {b = fsuc b} (<fsuc a<b) =
  ≤ᶠ-respects-fsuc (weaken<-pred a<b)
```

```
≈ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a ≈ᶠ b → b ≈ᶠ c → a ≈ᶠ c
≈ᶠ-trans ≈fzero ≈fzero = ≈fzero
≈ᶠ-trans (≈fsuc a≈b) (≈fsuc b≈c) = ≈fsuc (≈ᶠ-trans a≈b b≈c)
```

```
<ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a <ᶠ b → b <ᶠ c → a <ᶠ c
<ᶠ-trans <fzero (<fsuc b<c) = <fzero
<ᶠ-trans (<fsuc a<b) (<fsuc b<c) = <fsuc (<ᶠ-trans a<b b<c)
```

```
<≤ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a <ᶠ b → b ≤ᶠ c → a <ᶠ c
<≤ᶠ-trans a<b (inl b<c) = <ᶠ-trans a<b b<c
<≤ᶠ-trans <fzero (inr (≈fsuc b≈c)) = <fzero
<≤ᶠ-trans (<fsuc a<b) (inr (≈fsuc b≈c)) = <fsuc (<≤ᶠ-trans a<b (inr b≈c))
```

```
≤<ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a ≤ᶠ b → b <ᶠ c → a <ᶠ c
≤<ᶠ-trans (inl a<b) b<c = <ᶠ-trans a<b b<c
≤<ᶠ-trans (inr ≈fzero) <fzero = <fzero
≤<ᶠ-trans (inr (≈fsuc a≈b)) (<fsuc b<c) = <fsuc (≤<ᶠ-trans (inr a≈b) b<c)
```

```
≤ᶠ-trans : ∀ {x} {a : Fin x} {b : Fin y} {c : Fin z} → a ≤ᶠ b → b ≤ᶠ c → a ≤ᶠ c
≤ᶠ-trans (inl a<b) (inl b<c) = inl (<ᶠ-trans a<b b<c)
≤ᶠ-trans (inl a<b) (inr b≈c) = inl (<≤ᶠ-trans a<b (inr b≈c))
≤ᶠ-trans (inr a≈b) (inl b<c) = inl (≤<ᶠ-trans (inr a≈b) b<c)
≤ᶠ-trans (inr a≈b) (inr b≈c) = inr (≈ᶠ-trans a≈b b≈c)
```

```
<-suc : ∀ (a : Fin x) → a <ᶠ fsuc a 
<-suc fzero = <fzero
<-suc (fsuc a) = <fsuc (<-suc a)
```

```
≤-pred : ∀ {a : Fin x} {b : Fin y} → fsuc a ≤ᶠ fsuc b → a ≤ᶠ b
≤-pred (inl (<fsuc a<b)) = inl a<b
≤-pred (inr (≈fsuc a≈b)) = inr a≈b
```

```
fsuc≤fsuc : a ≤ᶠ b → fsuc a ≤ᶠ fsuc b
fsuc≤fsuc (inl a<b) = inl (<fsuc a<b)
fsuc≤fsuc (inr a≈b) = inr (≈fsuc a≈b)
```

```
≤ᶠ→<ᶠ : {a : Fin x} {b : Fin y} → a ≤ᶠ b → a <ᶠ fsuc b
≤ᶠ→<ᶠ {b = b} (inl a<b) = <ᶠ-trans a<b (<-suc b) 
≤ᶠ→<ᶠ (inr ≈fzero) = <fzero
≤ᶠ→<ᶠ (inr (≈fsuc a≈b)) = <fsuc (≤ᶠ→<ᶠ (inr a≈b))
```

```
<ᶠ→≤ᶠ : {a : Fin x} {b : Fin y} → a <ᶠ fsuc b → a ≤ᶠ b
<ᶠ→≤ᶠ {a = fzero} {fzero} a<b' = inr ≈fzero
<ᶠ→≤ᶠ {a = fzero} {fsuc b} 0<b' = inl <fzero
<ᶠ→≤ᶠ {a = fsuc a} {fsuc b} (<fsuc a<b) = fsuc≤fsuc (<ᶠ→≤ᶠ a<b)
```

```
¬a<a : {a : Fin x} → ¬ a <ᶠ a
¬a<a {a = fsuc a} (<fsuc a<a) = ¬a<a a<a
```

```
<ᶠ→≉ : {a : Fin x} {b : Fin y} → a <ᶠ b → a ≉ᶠ b
<ᶠ→≉ {a = fzero} {b = fsuc b} <fzero a≈b = fzero≉fsuc a≈b
<ᶠ→≉ {a = fsuc a} {b = fsuc b} (<fsuc a<b) a≈b =
  <ᶠ→≉ {a = a} {b = b} a<b (≈fsuc-injective a≈b)
```

```
<ᶠ→≢ : {a b : Fin x} → a <ᶠ b → a ≢ b
<ᶠ→≢ a<b = ≉ᶠ→≢ (<ᶠ→≉ a<b)
```

```
≤ᶠ→≯ᶠ : {a : Fin x} {b : Fin y} → a ≤ᶠ b → ¬ b <ᶠ a
≤ᶠ→≯ᶠ (inl (<fsuc a<b)) (<fsuc a>b) = ≤ᶠ→≯ᶠ (inl a<b) a>b
≤ᶠ→≯ᶠ (inr a≈b) a>b = <ᶠ→≉ a>b (≈fsym a≈b)
```

```
<ᶠ→≯ᶠ : {a : Fin x} {b : Fin y} → a <ᶠ b → ¬ b <ᶠ a
<ᶠ→≯ᶠ a<b b<a = ¬a<a  (<ᶠ-trans a<b b<a)
```

```
fsuc≤fsuc→<fsuc : (a≤b : a ≤ᶠ b) → ≤ᶠ→<ᶠ (fsuc≤fsuc a≤b) ≡ <fsuc (≤ᶠ→<ᶠ a≤b)
fsuc≤fsuc→<fsuc (inl x) = refl
fsuc≤fsuc→<fsuc (inr x) = refl
```

```
fin-restrict-< : ∀ {x} {b : Fin (suc x)} (a : Fin y)
               → a <ᶠ b → Fin x
fin-restrict-< {x = suc x} fzero <fzero = fzero
fin-restrict-< {x = suc x} (fsuc a) (<fsuc a<b) = fsuc (fin-restrict-< a a<b)
```

```
fin-restrict-≤ : ∀ {x} {b : Fin x} (a : Fin y)
               → a ≤ᶠ b → Fin x
fin-restrict-≤ a a≤b = fin-restrict-< a (≤ᶠ→<ᶠ a≤b)
```

```
fin-restrict-<≡fin-restrict-≤ 
  : ∀ {x} {y} → {b : Fin x} (a : Fin y) → (a≤b : a ≤ᶠ b)
  → fin-restrict-< a (≤ᶠ→<ᶠ a≤b) ≡ fin-restrict-≤ a a≤b
fin-restrict-<≡fin-restrict-≤ a a≤b =
  refl
```

```
fin-restrict' : ∀ {x} {b : Fin x} (a : Fin (suc x))
              → a ≤ᶠ b → Fin x
fin-restrict' {x = 0} {b} a x = b
fin-restrict' {x = suc x} {b = fsuc b} fzero (inl 0<b') = fzero
fin-restrict' {x = suc x} fzero (inr 0≈b) = fzero
fin-restrict' {x = suc x} {b = fsuc b} (fsuc a) (inl (<fsuc a<b)) = fsuc (fin-restrict' a (inl a<b))
fin-restrict' {x = suc x} {b = fzero} (fsuc a) (inr a'≈0) = absurd (fsuc≉fzero a'≈0)
fin-restrict' {x = suc x} {b = fsuc b} (fsuc a) (inr a'≈b') = fsuc (fin-restrict' a (inr (≈fsuc-injective a'≈b')))
```

```
case≤?ᶠ : {A : Type} {m : ℕ} (a b : Fin m) → A → A → A
case≤?ᶠ a b x y = case (a ≤?ᶠ b) of
  λ{ (fle _) → x
   ; (fgt _) → y }
```

```
≤?ᶠ-suc : {a : Fin x} {b : Fin y} → Bichotomyᶠ a b → Bichotomyᶠ (fsuc a) (fsuc b)  
≤?ᶠ-suc (fle a≤b) = fle (fsuc≤fsuc a≤b)
≤?ᶠ-suc (fgt a>b) = fgt (<fsuc a>b)
```

```
isProp≈ᶠ : {a : Fin x} {b : Fin y} → isProp (a ≈ᶠ b)
isProp≈ᶠ ≈fzero ≈fzero = refl
isProp≈ᶠ (≈fsuc u) (≈fsuc v) = cong ≈fsuc (isProp≈ᶠ u v)
```

```
isProp<ᶠ : {a : Fin x} {b : Fin y} → isProp (a <ᶠ b)
isProp<ᶠ <fzero <fzero = refl
isProp<ᶠ (<fsuc u) (<fsuc v) = cong <fsuc (isProp<ᶠ u v)
```

```
isProp≤ᶠ : {a : Fin x} {b : Fin y} → isProp (a ≤ᶠ b)
isProp≤ᶠ (inl u) (inl v) = cong inl (isProp<ᶠ u v)
isProp≤ᶠ (inl u) (inr v) = absurd (<ᶠ→≉ u v)
isProp≤ᶠ (inr u) (inl v) = absurd (<ᶠ→≉ v u)
isProp≤ᶠ (inr u) (inr v) = cong inr (isProp≈ᶠ u v)
```

```
isPropBichotomyᶠ : {a : Fin x} {b : Fin y} → isProp (Bichotomyᶠ a b)
isPropBichotomyᶠ (fle u) (fle v) = cong fle (isProp≤ᶠ u v)
isPropBichotomyᶠ (fle u) (fgt v) = absurd (≤ᶠ→≯ᶠ u v)
isPropBichotomyᶠ (fgt u) (fle v) = absurd (≤ᶠ→≯ᶠ v u)
isPropBichotomyᶠ (fgt u) (fgt v) = cong fgt (isProp<ᶠ u v)
```

```
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
```

```
≤?ᶠ-pred : (a : Fin x) (b : Fin y) → fsuc a ≤?ᶠ fsuc b ≡ ≤?ᶠ-suc (a ≤?ᶠ b)
≤?ᶠ-pred a b with a ≟ᶠ b
... | flt a<b = refl
... | feq a≈b = refl
... | fgt a>b = refl
```

```
≈ᶠ-inj : ∀ (a : Fin x) → finj a ≈ᶠ a
≈ᶠ-inj fzero = ≈fzero
≈ᶠ-inj (fsuc a) = ≈fsuc (≈ᶠ-inj a)
```

```
≈ᶠ-inject : ∀ y → (a : Fin x) → finject y a ≈ᶠ a
≈ᶠ-inject y fzero = ≈fzero
≈ᶠ-inject zero (fsuc a) = ≈fsuc (≈ᶠ-inject 0 a)
≈ᶠ-inject (suc y) (fsuc a) = ≈fsuc (≈ᶠ-inject (suc y) a)
```

```
<ᶠ-respects-≈ᶠ : ∀ {w x y z : ℕ}
               → {a : Fin w} {b : Fin x} {c : Fin y} {d : Fin z}
               → a ≈ᶠ b → b <ᶠ c → c ≈ᶠ d → a <ᶠ d
<ᶠ-respects-≈ᶠ ≈fzero <fzero (≈fsuc c≈d) = <fzero
<ᶠ-respects-≈ᶠ (≈fsuc a≈b) (<fsuc b<c) (≈fsuc c≈d) =
  <fsuc (<ᶠ-respects-≈ᶠ a≈b b<c c≈d)
```

```
<ᶠ-inject : (x' y' : ℕ) (a : Fin x) (b : Fin y) → a <ᶠ b → finject x' a <ᶠ finject y' b 
<ᶠ-inject x' y' a b a<b =
  <ᶠ-respects-≈ᶠ (≈ᶠ-inject x' a) a<b (≈fsym (≈ᶠ-inject y' b))
```

```
<ᶠ-inj-l : {a : Fin x} {b : Fin y} → a <ᶠ b → finj a <ᶠ b 
<ᶠ-inj-l a<b =
  <ᶠ-respects-≈ᶠ (≈ᶠ-inj _) a<b (≈refl)
import Cubical.Data.Nat as ℕ
open ℕ.ℕ
```

```
toℕ∘fromℕ≡id : {m : ℕ} → (n : ℕ) → (n<m : n < m) → toℕ {m} (fromℕ n n<m) ≡ n
toℕ∘fromℕ≡id {zero} n n<0 =
  absurd (¬-<-zero {n} n<0)
toℕ∘fromℕ≡id {suc m} zero 0<sm = refl
toℕ∘fromℕ≡id {suc m} (suc n) sn<sm =
  cong suc (toℕ∘fromℕ≡id n (pred-<-pred sn<sm))
```

```
toℕ<m : ∀ {m : ℕ} → (a : Fin m) → toℕ a < m 
toℕ<m {suc m} fzero = 0<suc m
toℕ<m {suc m} (fsuc a) = suc-<-suc (toℕ<m a)
```

```
finject-fsuc-reorder : ∀ {x y : ℕ} → (a : Fin x)
                      → finject y (fsuc a) ≡ fsuc (finject y a)
finject-fsuc-reorder {suc x} {zero} a = refl
finject-fsuc-reorder {suc x} {suc y} a = refl
finject-fsuc-reorder {zero} {suc y} a = refl
```

```
-- Like subst but computes on constructors. See std library.
fcast : (x ≡ y) → Fin x → Fin y
fcast {x = zero} {y = zero} p a = a
fcast {x = zero} {y = suc y} p a = absurd (ℕ.znots p)
fcast {x = suc x} {y = zero} p a = absurd (ℕ.snotz p)
fcast {x = suc x} {y = suc y} p fzero = fzero
fcast {x = suc x} {y = suc y} p (fsuc a) = fsuc (fcast (ℕ.injSuc p) a)
```

```
fcast-loop : (p : x ≡ x) → (a : Fin x) → fcast p a ≡ a
fcast-loop p fzero = refl
fcast-loop p (fsuc a) =
  cong fsuc (fcast-loop (cong ℕ.predℕ p) a)
```

```
fcast-irrelevant : (p q : x ≡ y) → (a : Fin x) → fcast p a ≡ fcast q a
fcast-irrelevant {x = zero} {y = zero} p q a = refl
fcast-irrelevant {x = zero} {y = suc y} p q a = absurd (ℕ.znots p)
fcast-irrelevant {x = suc x} {y = zero} p q a = absurd (ℕ.snotz p)
fcast-irrelevant {x = suc x} {y = suc y} p q fzero = refl
fcast-irrelevant {x = suc x} {y = suc y} p q (fsuc a) =
  cong fsuc (fcast-irrelevant (ℕ.injSuc p) (ℕ.injSuc q) a)
```

```
finject0≡fcast : {x : ℕ} (a : Fin x)
               → finject {x} zero a ≡ fcast (sym (+-zero x)) a
finject0≡fcast fzero = refl
finject0≡fcast (fsuc a) = cong fsuc (finject0≡fcast a)
```

```
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
```

```
_≈?ᶠ_ : ∀ {x} → (a : Fin x) (b : Fin y) → Dec (a ≈ᶠ b)
a ≈?ᶠ b with (a ≟ᶠ b)
... | flt a<b = no (<ᶠ→≉ a<b)
... | feq a≈b = yes a≈b
... | fgt b<a = no (≉fsym (<ᶠ→≉ b<a))
```

```
_≡?ᶠ_ : ∀ {x} → Discrete (Fin x)
a ≡?ᶠ b with (a ≟ᶠ b)
... | flt a<b = no (≉ᶠ→≢ (<ᶠ→≉ a<b))
... | feq a≈b = yes (≈ᶠ→≡ a≈b)
... | fgt b<a = no (≢sym (≉ᶠ→≢ (<ᶠ→≉ b<a)))
```

```
isSetFin : ∀ {x} → isSet (Fin x)
isSetFin = Discrete→isSet _≡?ᶠ_
```

```
subst-fsuc-reorder
  : ∀ {x y : ℕ} → (p : x ≡ y) → (a : Fin x)
  → transport (λ i → Fin (suc (p i))) (fsuc a)
  ≡ fsuc (transport (λ i → Fin (p i)) a)
subst-fsuc-reorder p a = transport-reorder Fin suc fsuc p a
```

```
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
```

```
fshift-injective : {x : ℕ} → (y : ℕ) → is-injective (fshift x {y})
fshift-injective {zero} y a b fa≡fb = fa≡fb
fshift-injective {suc x} y a b fa≡fb =
  fshift-injective {x} y a b (fsuc-injective fa≡fb)
```

```
subst-finject-reorder
  : ∀ {x y : ℕ} (z : ℕ) (p : x ≡ y) (a : Fin x)
  → subst (λ ○ → Fin (○ +ℕ z)) p (finject {x} z a)
  ≡ finject {y} z (subst Fin p a)
subst-finject-reorder z p a =
  transport-reorder Fin (_+ℕ z) (λ {w} b → finject {w} z b) p a
```

```
subst-fshift-reorder
  : ∀ {x y z : ℕ} → (p : x ≡ y) → (a : Fin x)
  → subst (λ ○ → Fin (z +ℕ ○)) p (fshift z {x} a)
  ≡ fshift z {y} (subst Fin p a)
subst-fshift-reorder {x} {y} {z} p a =
  transport-reorder Fin (z +ℕ_) (λ {w} b → fshift z b) p a
```

```
fzero-cong : {x y : ℕ} (p : x ≡ y)
           → (λ i → Fin (suc (p i))) [ fzero {x} ≡ fzero {y} ]
fzero-cong {x} {y} p i = fzero {p i}
```

```
fzero≡subst-fzero : {x y : ℕ} (p : x ≡ y)
                  → fzero {y} ≡ subst (Fin ∘ suc) p (fzero {x})
fzero≡subst-fzero {x} {y} p = resubst (Fin ∘ suc) (λ z → fzero {z}) p
```

```
fzero≡cast-fzero : {x y : ℕ} (p : x ≡ y)
                 → fzero {y} ≡ fcast (cong suc p) (fzero {x})
fzero≡cast-fzero p = refl
```

```
ℕ+1 : ∀ {x : ℕ} → x ℕ.+ 1 ≡ suc x
ℕ+1 {x} = ℕ.+-comm x 1
```

```
finject1≡finj : {x : ℕ} (a : Fin x)
               → finject 1 a ≡ subst Fin (sym ℕ+1) (finj a)
finject1≡finj {suc x} fzero = fzero≡subst-fzero (sym ℕ+1)
finject1≡finj {suc x} (fsuc a) =
  finject 1 (fsuc a) ≡⟨ finject-fsuc-reorder a ⟩
  fsuc (finject 1 a) ≡⟨ cong fsuc (finject1≡finj a) ⟩
  fsuc (subst Fin (sym ℕ+1) (finj a)) ≡⟨ sym (subst-fsuc-reorder (sym ℕ+1) (finj a)) ⟩
  subst Fin (sym ℕ+1) (fsuc (finj a)) ≡⟨ refl ⟩
  subst Fin (sym ℕ+1) (finj (fsuc a)) ▯
```

```
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
```

```
≉fsuc
  : ∀ {x : ℕ} → {b a : Fin (suc x)} → (a≉b : a ≉ᶠ b)
  → fsuc a ≉ᶠ fsuc b
≉fsuc a≉b (≈fsuc a≈b) = a≉b a≈b
```

```
≉pred : ∀ {x y} {a : Fin x} {b : Fin y} → fsuc a ≉ᶠ fsuc b → a ≉ᶠ b
≉pred a'≉b' a≈b = a'≉b' (≈fsuc a≈b)
```

```
finj-injective : {x : ℕ} → is-injective (finj {x})
finj-injective fzero fzero fx≡fy = refl
finj-injective fzero (fsuc y) fx≡fy = absurd (fzero≢fsuc fx≡fy)
finj-injective (fsuc x) fzero fx≡fy = absurd (fsuc≢fzero fx≡fy)
finj-injective (fsuc x) (fsuc y) fx≡fy =
  cong fsuc (finj-injective x y (fsuc-injective fx≡fy))
```

```
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
```

```
toℕ-finject : {x : ℕ} (y : ℕ) (a : Fin x) → toℕ (finject y a) ≡ toℕ a
toℕ-finject y fzero = refl
toℕ-finject y (fsuc a) = cong suc (toℕ-finject y a)
```

```
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
```

```
toℕ-finject-< : {x : ℕ} (y : ℕ) (a : Fin x) → toℕ (finject y a) < x
toℕ-finject-< {suc x} y fzero = 0<suc x
toℕ-finject-< {suc x} y (fsuc a) = suc-<-suc (toℕ-finject-< y a)
```

```
toℕ-fshift-≥ : (x : ℕ) {y : ℕ} (a : Fin y) → toℕ (fshift x a) ≥ x 
toℕ-fshift-≥ zero a = zero-≤
toℕ-fshift-≥ (suc x) a = suc-≤-suc (toℕ-fshift-≥ x a)
```

```
finj∘fsuc≈fsuc∘finj : ∀ {x} (a : Fin (suc x)) → finj (fsuc a) ≈ᶠ fsuc (finj a)
finj∘fsuc≈fsuc∘finj a = ≈refl
```

```
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
    ≡⟨ {!refl!} ⟩
  fsuc (subst Fin (ℕ.+-assoc x (suc y) z) (finject (suc y +ℕ z) a))
    ≡⟨ sym (subst-fsuc-reorder (ℕ.+-assoc x (suc y) z) (finject (suc y +ℕ z) a)) ⟩
  subst Fin (ℕ.+-assoc (suc x) (suc y) z) (fsuc (finject (suc y +ℕ z) a))
    ≡⟨ refl ⟩
  subst Fin (ℕ.+-assoc (suc x) (suc y) z) (finject (suc y +ℕ z) (fsuc a)) ▯
```

```
subst0≡fcast0 : {x y : ℕ} (p : x ≡ y)
              → subst (Fin ∘ suc) p (fzero {x}) ≡ fcast (cong suc p) (fzero {x})
subst0≡fcast0 p = sym (fzero≡subst-fzero p)
```

```
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
```

```
finject-+' : ∀ (x y z : ℕ) → (a : Fin x)
           → finject z (finject y a)
           ≡ fcast (ℕ.+-assoc x y z) (finject (y ℕ.+ z) a)
finject-+' x y z a = {!!}
```

```
open _∖_
```

```
module DelZeroSuc {x : ℕ} (b :  ⟦ x ⟧) where
  B : (suc x ∖ fzero)
  B = fsuc b — fzero≢fsuc {i = b}
```

```
  del-zero-suc : del fzero B ≡ b
  del-zero-suc with (del fzero B) | inspect (del fzero) B
  ... | fzero | [ p ]ᵢ = sym p
  ... | fsuc A | [ p ]ᵢ = sym p
```

```
open DelZeroSuc using (del-zero-suc)
```

```
del-suc-zero : ∀ {x} (a : ⟦ suc x ⟧)
             → del (fsuc a) (fzero — fsuc≢fzero {i = a}) ≡ fzero
del-suc-zero a = refl
```

```
del-suc-suc : ∀ {x} (a b : ⟦ suc x ⟧) → (a'≢b' : fsuc a ≢ fsuc b)
             → del (fsuc a) (fsuc b — a'≢b')
             ≡ fsuc (del a (b — ≢cong fsuc a'≢b'))
del-suc-suc {zero} fzero fzero a'≢b' =
  absurd (a'≢b' refl)
del-suc-suc {suc x} a b a'≢b' = refl
```

```
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
del-inj {x = suc x} (fsuc a) (fsuc b — a≢b) (fsuc c — a≢c) b'≡c'
  = cong fsuc (del-inj {x = x} a (b — ≢cong fsuc a≢b) (c — {!!}) {!!})
```

```
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
```
