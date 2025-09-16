<!--
```
module Dissertation.Function where

open import Cubical.Core.Primitives
open import Cubical.Data.Empty
open import Cubical.Data.Equality.Base using (id)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import VSet.Prelude
open import VSet.Data.Sum.Properties
```
-->

\begin{verbatim}[hide]
module DissertationTex.Function where

open import Cubical.Core.Primitives
open import Cubical.Data.Empty
open import Cubical.Data.Equality.Base using (id)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import VSet.Prelude
open import VSet.Data.Sum.Properties
\end{verbatim}

# Function

```
private
  variable
    a b c d : Level
    A : Type a
    B : Type b
    C : Type c
    D : Type d
```

## Injectivity

```
is-injective : {X Y : Type} → (f : X → Y) → Type
is-injective {X} f = ∀ (x y : X) → f x ≡ f y → x ≡ y

_↣_ : (X Y : Type) → Type
X ↣ Y = Σ (X → Y) is-injective

↣-id : (X : Type) → X ↣ X
↣-id X = (λ x → x) , (λ x y p → p)
```

```
transport-inj
  : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : A ≡ B)
  → transport p x ≡ transport p y
  → x ≡ y
transport-inj {x = x} {y = y} p q =
  x ≡⟨ sym (transport⁻Transport p x) ⟩
  transport (sym p) (transport p x) ≡⟨ cong (transport (sym p)) q ⟩
  transport (sym p) (transport p y) ≡⟨ transport⁻Transport p y ⟩
  y ∎
```

## Isomorphisms as First-Class Data

```
mkIso : {A B : Type}
      → (f : A → B) → (g : B → A)
      → f ∘ g ≡ id → g ∘ f ≡ id
      → Iso A B
mkIso {A} {B} f g ri li =
  iso f g r l
  where
    l : (a : A) → g (f a) ≡ a
    l a = cong (λ ○ → ○ a) li
    r : (b : B) → f (g b) ≡ b
    r b = cong (λ ○ → ○ b) ri

flip-↔ : (A ↔ B) → (B ↔ A)
flip-↔ A↔B = invIso A↔B

infixl 9 _↔∘↔_

_↔∘↔_ : (B ↔ C) → (A ↔ B) → (A ↔ C)
g ↔∘↔ f = compIso f g
```

```
module _ where
  double-flip : ∀ {A B} (R : A ↔ B) → (flip-↔ {B} {A} (flip-↔ {A} {B} R)) ≡ R
  double-flip R i .fun = fun R
  double-flip R i .inv = inv R
  double-flip R i .rightInv = rightInv R
  double-flip R i .leftInv = leftInv R

  flip-IsId : ∀ {A B} (R : A ↔ B) → ((flip-↔ R) ↔∘↔ R) ^ ≡ id
  flip-IsId R i x = leftInv R x i
```


```
↔to↣ : (A ↔ B) → (A ↣ B)
↔to↣ f =
  let inj : is-injective (fun f)
      inj x y eq =
        x
          ≡⟨ sym (cong (λ ○ → ○ x) (linv f)) ⟩
        (inv f ∘ fun f) x
          ≡⟨ refl ⟩
        inv f (fun f x)
          ≡⟨ cong (inv f) eq ⟩
        inv f (fun f y)
          ≡⟨ refl ⟩
        (inv f ∘ fun f) y
          ≡⟨ cong (λ ○ → ○ y) (linv f) ⟩
        y ▯
  in fun f , inj
```

```
≡to↣ : ∀ {A B} → A ≡ B → A ↣ B
≡to↣ p = transport p , λ x y q → transport-inj p q

refl-to-↣-is-id : ∀ {A} → fst (≡to↣ (refl {x = A})) ≡ id
refl-to-↣-is-id =
  funExt (λ x →
    fst (≡to↣ refl) x ≡⟨ refl ⟩
    transport refl x ≡⟨ transportRefl x ⟩
    x ▯)
```

## Composition of Injections

```
infixl 5 _↣∘↣_

_↣∘↣_ : (B ↣ C) → (A ↣ B) → (A ↣ C)
(f , inj₁) ↣∘↣ (g , inj₂) = (f ∘ g) , λ x y eq → inj₂ _ _ (inj₁ _ _ eq)

↣∘↣-idR : ∀ {X Y : Type} (f : X ↣ Y) → f ↣∘↣ ↣-id X ≡ f
↣∘↣-idR (f , f-inj) = refl

↣∘↣-idL : ∀ {X Y : Type} (f : X ↣ Y) → ↣-id Y ↣∘↣ f ≡ f
↣∘↣-idL (f , f-inj) = refl

↣∘↣-assoc : ∀ {A B C D : Type} (h : C ↣ D) (g : B ↣ C) (f : A ↣ B)
          → h ↣∘↣ (g ↣∘↣ f) ≡ (h ↣∘↣ g) ↣∘↣ f
↣∘↣-assoc h g f = refl
```

## 'Lifting' Injections Across Sums

```
↣-map-⊎ : {A B C D : Type ℓ-zero} → (A ↣ B) → (C ↣ D) → ((A ⊎ C) ↣ (B ⊎ D))
↣-map-⊎ {A} {B} {C} {D} f g = h , inj
  where
    h : (A ⊎ C) → (B ⊎ D)
    h = ⊎-map (fst f) (fst g)

    inj : (x y : A ⊎ C) → h x ≡ h y → x ≡ y
    inj (inl a₁) (inl a₂) hx≡hy =
        cong inl
      $ snd f a₁ a₂
      $ inl-injective (fst f a₁) (fst f a₂)
      $ hx≡hy
    inj (inl a₁) (inr c₂) hx≡hy =
      absurd (inl≢inr (fst f a₁) (fst g c₂) hx≡hy)
    inj (inr c₁) (inl a₂) hx≡hy =
      absurd (inl≢inr (fst f a₂) (fst g c₁) (sym hx≡hy))
    inj (inr c₁) (inr c₂) hx≡hy =
        cong inr
      $ snd g c₁ c₂
      $ inr-injective (fst g c₁) (fst g c₂)
      $ hx≡hy
```

## Relating Identity Functions `transport`.

```
id≡transport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
             → (λ i → A → p i) [ id ≡ transport p ]
id≡transport p = funExt (transport-filler p)

id≡subst : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A}
        → (B : A → Type ℓ') (p : x ≡ y)
        → (λ i → B x → B (p i)) [ id ≡ subst B p ]
id≡subst B p = funExt (subst-filler B p)
```

```
id≡subst' : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A}
        → (B : A → Type ℓ') (p : x ≡ y)
        → (λ i → B (p i) → B x) [ id ≡ subst B (sym p) ]
id≡subst' B p = {!subst-filler B ?!}
```
