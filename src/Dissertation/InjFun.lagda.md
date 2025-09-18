<!--
```
module Dissertation.InjFun where

open import Compat.1Lab.Path using (cong₂-∙)
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.HLevels
open import VSet.Data.Fin.Base hiding (⟦_⟧)
open import VSet.Data.Fin.Properties
open import VSet.Data.Sum.Properties
open import VSet.Function.Iso using (linv; rinv; _^; _⁻¹)
open import VSet.Function.Injection using (transport-inj)
open import VSet.Prelude
private
  variable
    A B C D : Type
```
-->


# Depdendent Sum Representation of Injective Functions

## Definition of `InjFun`

We begin by defining the concept of injectivity. The standard way to
define a injective function in type theory is to construct, using
a dependent sum (`Σ`), the notion of a function paired with a proof of
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

Now we can define an alias for `Fin` and a type constructor call
`InjFun`, with a square-bracket syntax, which is the function represention of finite injective
functions:

```
⟦_⟧ : ℕ → Type
⟦_⟧ = Fin

-- 'InjFun'
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

## Composition of Injective Function

We define composition on injective functions, `↣`, by composing the
underlying functions and chaining the injectivity proof. The unit and
associativity laws hold by definitional equality in this encoding, so
the proofs are `refl`. This is intentional: we picked a representation
that makes the algebra easy, and Agda is powerful enough to recognize
this. These four lemmas are most of what we need to construct a category of
injective functions.

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

We additionally write a function to convert between *paths* and injections.
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

## Properties of `InjFun`

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

The importance of this lemma is it means that there at most one way
that any particular function can be represented in as an injective
function, so a pair of injective finite functions are equal if and
only if their injection form are equal. It also lets us
prove the following lemma that each `InjFun` is a set, meaning that
there are no 'hidden' homotopic behaviour other than simple equality
between members with the same type.
```
isSetInjFun : {m n : ℕ} → isSet [ m ↣ n ]
isSetInjFun {m} {n} =
  isSetΣ (isSet→ isSetFin)
         (λ f → isProp→isSet (isProp-is-injective f))
```

## Equivalence Relation on InjFun

We define a heterogeneous relation on `InjFun` that allows us to
compare two injective functions across equal types which might not be
definitionally equal, meaning Agda can't normalize them to the same value.
For example, `X + Y ≡ Y + X` for `X Y : ℕ` in the sense of path
equality, but they don't both reduce to the same normal form.
```
infix 8 _≈_

record _≈_ {A B X Y : ℕ} (f : [ A ↣ X ]) (g : [ B ↣ Y ]) : Type where
  field
    p : A ≡ B
    q : X ≡ Y
    path : (λ i → cong₂ FinFun p q i) [ fst f ≡ fst g ]
```

We then show that is is an equivalence relation, that is a relation that is (a) reflexive, (b) symmetric, and (c) transitive. This means informally that for all
`A B C X Y Z : ℕ`, `f : [ A ↣ X ]`, `g : [ B ↣ Y ]`, `g : [ C ↣ Z ]`,

 (a) `f ≡ f`

 (b) `f ≡ g → g ≡ f`

 (c) `f ≡ g → g ≡ h → f ≡ h`

```
≈refl : {A X : ℕ} (f : [ A ↣ X ]) → f ≈ f
≈refl {A} {X} f = record
  { p = refl
  ; q = refl
  ; path = λ i x → fst f x
  }

≈sym : ∀ {A B X Y : ℕ} {f : [ A ↣ X ]} {g : [ B ↣ Y ]} → f ≈ g → g ≈ f
≈sym {A} {B} {X} {Y} {f} {g} f≈g = record
  { p = sym p 
  ; q = sym q
  ; path = λ i → path (~ i)
  }
  where
    open _≈_ f≈g
```

Transitivity is the only difficut one. We construct it in a module for
convenience. TODO: Insert diagram
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

  infixl 4 _∘≈_ 
  _∘≈_ : f ≈ h
  _∘≈_ = ≈trans

open Trans using (≈trans; _∘≈_) public
```

We also define reverse composition, and a path syntax derived from the
one in the cubical standard library for `≡`.

```
-- reverse composition
infixl 4 _≈∘_
_≈∘_ : {A B C X Y Z : ℕ}
       {f : [ A ↣ X ]}
       {g : [ B ↣ Y ]}
       {h : [ C ↣ Z ]}
       (f≈g : f ≈ g) (g≈h : g ≈ h) → f ≈ h
f≈g ≈∘ g≈h = ≈trans g≈h f≈g

infixr 2 _≈⟨_⟩_
_≈⟨_⟩_ : {A B C X Y Z : ℕ}
       → (f : [ A ↣ X ]) → {g : [ B ↣ Y ]} → {h : [ C ↣ Z ]}
       → f ≈ g → g ≈ h → f ≈ h
_ ≈⟨ f≈g ⟩ g≈h = g≈h ∘≈ f≈g

infix 3 _∎
_∎ : {A X : ℕ} → (f : [ A ↣ X ]) → f ≈ f
f ∎ = ≈refl f
```

Finally we construct a transport operation for `InjFun` types. (See Section \ref{operations-on-paths}.)
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

Next we define a filler to show that a function has a path to its
transported version.
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

`from≡` is for the simple case where the indexes are the same at both
ends. In this case, `path` is a simple (non-dependent) path.
```
from≡ : ∀ {A X : ℕ} → {f g : [ A ↣ X ]}
      → fst f ≡ fst g → f ≈ g
from≡ path = record
  { p = refl
  ; q = refl
  ; path = path
  }
```

After using this definition for a bit, I found that support for
dependent paths, which are paths in which the type of the path
transforms along with the value, in the cubical library is
significantly behind what is available as 'simple' (non-dependent)
paths.

## Isomorphisms

We will also be making use of isomorphism types. These are an
essential component of cubical type theory, providing a way to
formalize the idea that two types can be considered equivalent when
there exist mutually inverse functions between them. `Iso A B` is the
isomorphism type between `A` and `B`, often drawn as `A ≅ B` in
mathematical notation. In this context, I will use a slightly differnt
convention and notation to access the standard defnition. I use `A ≅ B` to
denote the isomorphism type, and have different accessors. Suppose `f
: A ≅ B` is an isomorphism. Then it has four components:
 - `f ^ : A → B` - the forward function
 - `f ⁻¹ : B → A` - the inverse function
 - `rinv : f ^ ∘ f ⁻¹ ≡ id` - right inverse
 - `linv : f ⁻¹ ∘ f ^ ≡ id` - left inverse

rinv and linv are the function extensionality version of the one in the definition of `Iso`.

infix 1 _≅_

```
_≅_ : (A B : Type) → Type
A ≅ B = Iso A B
```

We introduce an adapter. A symmetric function `flip-≅`, and a
transitive function `_≅∘≅_`.
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

flip-≅ : (A ≅ B) → (B ≅ A)
flip-≅ A≅B = invIso A≅B

infixl 9 _≅∘≅_

_≅∘≅_ : (B ≅ C) → (A ≅ B) → (A ≅ C)
g ≅∘≅ f = compIso f g
```

Next we create a function to convert between isomorphisms and
injections.

```
≅to↣ : (A ≅ B) → (A ↣ B)
≅to↣ f =
  fun f , inj
  where
    open Iso
    inj : is-injective (fun f)
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

```

## Coproduct Map for Injective Functions

This construction defines an injection on a sum type by combining
injections for each summand. The mapping function, `⊎-map`, applies
the respective injections to either side of the sum. Injectivity is
proven by a case analysis: (a) `inl` and `inr` are disjoint, so their
images can't clash; (b) if both inputs come from the same side,
injectivity follows from the branch's injectivity and the fact that
constructors themselves are injective. The proof utilizes previously
established lemmas about sums.
```
↣-map-⊎ : {A B C D : Type} → (A ↣ B) → (C ↣ D) → ((A ⊎ C) ↣ (B ⊎ D))
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

## Relating Identity Functions to `transport`

Te final equalities of this section export the idea that `transport p`
and `subst B p` are *paths of functions* (i.e., the identity deforms
into the transport operator). These are obtained from
`transport-filler` using the function extensionality principle
(`funExt`).

```
id≡transport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
             → (λ i → A → p i) [ id ≡ transport p ]
id≡transport p = funExt (transport-filler p)

id≡subst : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A}
        → (B : A → Type ℓ') (p : x ≡ y)
        → (λ i → B x → B (p i)) [ id ≡ subst B p ]
id≡subst B p = funExt (subst-filler B p)
```
