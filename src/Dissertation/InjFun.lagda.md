<!--
```
module Dissertation.InjFun where

open import Compat.1Lab.Path using (cong₂-∙)
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.HLevels
open import VSet.Data.Fin
open import VSet.Data.Fin.Base
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Prelude
```
-->

\begin{verbatim}[hide]
module DissertationTex.InjFun where

open import Compat.1Lab.Path using (cong₂-∙)
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.HLevels
open import VSet.Data.Fin
open import VSet.Data.Fin.Base
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Prelude
\end{verbatim}

# Depdendent Sum Representation of Injective Functions

Recall that `_↣_` is defined

We begin by defining the concept of injectivity. Then construct, using
a dependent sum `Σ` the notion of a function paired with a proof of
injectivity. Next we construct a simple injective function, `↣-id`,
which is made up of the identity function, paired with a trivial proof
that `id` is in fact injective. The notation for `_↣_` comes from the
categroy theoretic notation of a monic arrow.
```
is-injective : {X Y : Type} → (f : X → Y) → Type
is-injective {X} f = ∀ (x y : X) → f x ≡ f y → x ≡ y

_↣_ : (X Y : Type) → Type
X ↣ Y = Σ (X → Y) is-injective

↣-id : (X : Type) → X ↣ X
↣-id X = (λ x → x) , (λ x y p → p)
```
Next we apply that in the conext of `Fin`-injective functions. This
makes up our alternative definition to `Inj` of an injective
function. I believe that these two definitions are isomorphic, however
I did not get time to finish the proof of this.

```
[_↣_] : ℕ → ℕ → Type
[ X ↣ Y ] = ⟦ X ⟧ ↣ ⟦ Y ⟧
```

Note that the notation `⟦_⟧` is an alias for `Fin`, used to
suggest the notion that `Fin` is a function from the objects of a
category (`ℕ`) to the sets that those objects denote. It is used to
hint at the notion of 'semantic brackets' from denotational semantics.
We also use capital letters to represent the indexes in this section
to hint that they are objects in a category, and not simply naturals.

We construct a helper function for the function part of `[_↣_]`.
```
FinFun : ∀ (A B : ℕ) → Type
FinFun A B = ⟦ A ⟧ → ⟦ B ⟧
```

Next we show that `is-injective` is a proposition when applied to a
`FinFun`. This is done by making use of a chain of library lemmas that
strip off one lambda/`Π` at a time, before using the fact that `Fin`
is a set, and implicitly using the fact that `x ≡ y` is a proposition
whenever the containing type is a set.

%TODO: Define prop and set
```
isProp-is-injective : {m n : ℕ} → (f : FinFun m n) → isProp (is-injective f)
isProp-is-injective {m} f = isPropΠ λ x → isPropΠ λ y → isProp→ (isSetFin x y)
```

The importance of this lemma is it means that there is only one way
that any particular function can be represented in. It also lets us
prove the following lemma. (NB. FinFun is used incorrectly
interchangably with `[_↣_]` thoughout the development.)
```
isSetInjFun : {m n : ℕ} → isSet [ m ↣ n ]
isSetInjFun {m} {n} =
  isSetΣ (isSet→ isSetFin)
         (λ f → isProp→isSet (isProp-is-injective f))
```

# Equivalence Relation on InjFun

We define a heterogeneous relation on 
```
infix 8 _≈_

record _≈_ {A B X Y : ℕ} (f : [ A ↣ X ]) (g : [ B ↣ Y ]) : Type where
  field
    p : A ≡ B
    q : X ≡ Y
    path : (λ i → cong₂ FinFun p q i) [ fst f ≡ fst g ]
```

```
≈refl : {A X : ℕ} (f : [ A ↣ X ]) → f ≈ f
≈refl {A} {X} f = record
  { p = refl
  ; q = refl
  ; path = λ i x → fst f x
  }
```

```
≈sym : ∀ {A B X Y : ℕ} {f : [ A ↣ X ]} {g : [ B ↣ Y ]} → f ≈ g → g ≈ f
≈sym {A} {B} {X} {Y} {f} {g} f≈g = record
  { p = sym p 
  ; q = sym q
  ; path = λ i → path (~ i)
  }
  where
    open _≈_ f≈g
```

```
module Trans {A B C X Y Z : ℕ}
           {f : [ A ↣ X ]}
           {g : [ B ↣ Y ]}
           {h : [ C ↣ Z ]}
           (g≈h : g ≈ h) (f≈g : f ≈ g) where

  open _≈_ f≈g renaming (p to p1; q to q1; path to path1)
  open _≈_ g≈h renaming (p to p2; q to q2; path to path2)
  r1 : FinFun A X ≡ FinFun B Y
  r1 i = FinFun (p1 i) (q1 i)
  r2 : FinFun B Y ≡ FinFun C Z
  r2 i = FinFun (p2 i) (q2 i)
  ≈trans : f ≈ h
  ≈trans = record
    { p = p1 ∙ p2
    ; q = q1 ∙ q2
    ; path = path'
    }
    where
      c2 : cong₂ FinFun (p1 ∙ p2) (q1 ∙ q2) ≡
           cong₂ FinFun p1 q1 ∙ cong₂ FinFun p2 q2
      c2 = cong₂-∙ FinFun p1 p2 q1 q2
      path : (λ j → (cong₂ FinFun p1 q1 ∙ cong₂ FinFun p2 q2) j) [ fst f ≡ fst h ]
      path = compPathP path1 path2
      path' : (λ j → (cong₂ FinFun (p1 ∙ p2) (q1 ∙ q2)) j) [ fst f ≡ fst h ]
      path' = subst⁻ (λ ○ → (λ j → ○ j) [ fst f ≡ fst h ]) c2 path
```

```
  infixl 4 _∘≈_ 
  _∘≈_ : f ≈ h
  _∘≈_ = ≈trans
```

```
open Trans using (≈trans; _∘≈_) public
```

```
-- reverse composition
infixl 4 _≈∘_
_≈∘_ : {A B C X Y Z : ℕ}
       {f : [ A ↣ X ]}
       {g : [ B ↣ Y ]}
       {h : [ C ↣ Z ]}
       (f≈g : f ≈ g) (g≈h : g ≈ h) → f ≈ h
f≈g ≈∘ g≈h = ≈trans g≈h f≈g
```

```
infixr 2 _≈⟨_⟩_
_≈⟨_⟩_ : {A B C X Y Z : ℕ}
       → (f : [ A ↣ X ]) → {g : [ B ↣ Y ]} → {h : [ C ↣ Z ]}
       → f ≈ g → g ≈ h → f ≈ h
_ ≈⟨ f≈g ⟩ g≈h = g≈h ∘≈ f≈g
```

```
infix 3 _∎
_∎ : {A X : ℕ} → (f : [ A ↣ X ]) → f ≈ f
f ∎ = ≈refl f
```

```
≈transport : ∀ {A B X Y : ℕ} → A ≡ B → X ≡ Y → [ A ↣ X ] → [ B ↣ Y ]
≈transport {A = A} {B = B} p q f = X↣Y ↣∘↣ f ↣∘↣ B↣A
  where
    B↣A = ≡to↣ (cong Fin (sym p))
    X↣Y = ≡to↣ (cong Fin q)
```

```
≈transport-fun : ∀ {A B X Y : ℕ} → A ≡ B → X ≡ Y
               → (⟦ A ⟧ → ⟦ X ⟧) → ⟦ B ⟧ → ⟦ Y ⟧
≈transport-fun p q f =
  subst Fin q ∘ f ∘ subst Fin (sym p)
```

```
≈transport-filler : ∀ {A B X Y : ℕ} → (p : A ≡ B) → (q : X ≡ Y)
                  → (f : [ A ↣ X ]) → f ≈ ≈transport p q f
≈transport-filler {A = A} {B} {X} {Y} p q f =
  record { p = p ; q = q ; path = path }
  where
    B↣A = ≡to↣ (cong Fin (sym p))
    X↣Y = ≡to↣ (cong Fin q)
    P = cong₂ FinFun p q
    path : (λ i → cong₂ FinFun p q i)
      [ fst f
      ≡ subst Fin q ∘ fst f ∘ subst Fin (sym p)
      ]
    path = subst2-filler FinFun p q (fst f)
```

```
from≡ : ∀ {A X : ℕ} → {f g : [ A ↣ X ]}
      → fst f ≡ fst g → f ≈ g
from≡ path = record
  { p = refl
  ; q = refl
  ; path = path
  }
```

```
is-transport : ∀ {X Y : ℕ} → (f : [ X ↣ Y ]) → Type
is-transport {X} {Y} f = Σ[ p ∈ X ≡ Y ] fst f ≡ subst Fin p
```

