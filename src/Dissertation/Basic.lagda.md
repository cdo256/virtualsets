<!--
```
module Dissertation.Basic where

open import Agda.Primitive
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (rec to absurd) hiding (elim)
open import Cubical.Data.Equality.Base public using (id)
open import Cubical.Data.Maybe
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Sum public renaming (rec to ⊎-rec; elim to ⊎-elim; map to ⊎-map)
open import Cubical.Data.Unit.Base public renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Function public hiding (flip)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude renaming (_∎ to _▯)
  hiding (transport; transport-filler)
open import Cubical.Foundations.Transport
  hiding (transpEquiv)
open import Cubical.Relation.Nullary
open import VSet.Function.Iso
open import VSet.Function.Injection
open import Cubical.Data.Sum
open import VSet.Data.Fin.Base
open import Cubical.Data.Nat.Base
private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
```
-->

\begin{verbatim}[hide]
module DissertationTex.Basic where

open import Agda.Primitive
open import Cubical.Core.Primitives
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (rec to absurd) hiding (elim)
open import Cubical.Data.Equality.Base public using (id)
open import Cubical.Data.Maybe
open import Cubical.Data.Prod hiding (map)
open import Cubical.Data.Sum public renaming (rec to ⊎-rec; elim to ⊎-elim; map to ⊎-map)
open import Cubical.Data.Unit.Base public renaming (Unit to ⊤)
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Function public hiding (flip)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude renaming (_∎ to _▯)
  hiding (transport; transport-filler)
open import Cubical.Foundations.Transport
  hiding (transpEquiv)
open import Cubical.Relation.Nullary
open import VSet.Function.Iso
open import VSet.Function.Injection
open import Cubical.Data.Sum
open import VSet.Data.Fin.Base
open import Cubical.Data.Nat.Base
private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
\end{verbatim}

# Foundational Definitions

## Path Utilities

We will now begin the construction, starting with functions related to
paths. In homotopy type theory, a path is essentially a proof of
equality. Here `ℓ` is a *level* of Grothenieck universe. It can safely
be ignored on first reading. `Type` is a generalization of `Set`. For
our purposes the distinction doesn't mattter.

We define the negation of a path in the standard way, as a proof
that the existence of the path is absurd.
```
_≢_ : ∀ {ℓ} {A : Type ℓ} → (x y : A) → Type ℓ
x ≢ y = x ≡ y → ⊥
```

We then define two convenience functions on `≢`, the symmetric form,
and conjugation, which uses `cong` to show that `≢` is injective.
```
≢sym : {A : Type ℓ} {x y : A} → x ≢ y → y ≢ x
≢sym x≢y y≡x = x≢y (sym y≡x)

≢cong : ∀ {A B : Type} {x y : A} (f : A → B) → f x ≢ f y → x ≢ y
≢cong {A} {B} {x} {y} f fx≢fy x≡y = fx≢fy (cong f x≡y)
```

Next we introduce some foundational functions that are present in the
Agda Cubical library.
Transport is the operation used to map along paths. Is says that if
you have some type, then you can explicitly map every element of `A`
to some equivalent element in `B`. (Type below copied from Agda
Cubical library Cublical/Foundations/Prelude).
```
transport : {A B : Type ℓ} → A ≡ B → A → B
transport = _
```

Transport filler is a dependent path between a certain `x` in `A` and
the explicit transport of `x` along a path. We will use this to
construct a paths between objects and transports of those objects.
(Type below copied from Agda Cubical library
Cublical/Foundations/Prelude). It amounts to constructing a triangle
where the bottom left and right vertices are `x`, the top right vertex
is `transport p x`. The bottom edge is `refl` on `x`, the right edge is `p`
and the contents of the triangle, the 'fill' form the dependent path. 
```
transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
                 → PathP (λ i → p i) x (transport p x)
transport-filler = _
```

Returning to my definitions, we introduce a simple lemma that states
that cancels a `subst` with `subst` on the inverse path.
```
subst-inv : ∀ {A : Type} {x y : A} (B : A → Type) (p : x ≡ y) → (pa : B y)
          → subst B p (subst B (sym p) pa) ≡ pa
subst-inv {A} {x} {y} B p a =
  subst B p (subst B (sym p) a) ≡⟨ refl ⟩
  subst B p (transport (λ i → B (p (~ i))) a)
    ≡⟨ transportTransport⁻ (λ i → B (p i)) a ⟩
  a ▯
```

Then we define a Singleton type. A singleton is HoTT is an element `x` in
a type `A` together with a proof that all other elements in the type are
equal to that element. Note that this is exactly the same as saying
that `A` is contractable with an explicit witness `x`. (Definition
copied from 1Lab).
```
Singleton : ∀ {ℓ} {A : Type ℓ} → A → Type _
Singleton x = Σ[ y ∈ _ ] x ≡ y
```

We can make use of this to create a more convenient `inspect` function.
`inspect'` takes a value and gives another member of that type
together with a proof that they are both the same. Using this in a
`with` clause lets us pattern match on `x` and have a proof that `x`
is equal to it's epanded form, which is helpful for proving identities.
```
inspect' : ∀ {ℓ} {A : Type ℓ} (x : A) → Singleton x
inspect' x = x , refl
```

Next we will introduce a few complex looking helper functions. These
all work using the same core idea. We want to show and identity which
involves a transport operation, but to prove transport operations are
equal we have to use `transport-filler` (discussed earlier in this
section). As motivation, we are going to want to be able to 'swap' the
order of application of a `subst` and some constructor, or function, say
`fsuc`, the finite set successor (introduced later). Because both
`fsuc` and `subst` have a different type to the input, you can't just
swap their application order directly, you need to adjust the types on
both sides. Consider the following lemma,

```
subst-fsuc-reorder
  : ∀ {x y : ℕ} → (p : x ≡ y) → (a : Fin x)
  → subst (Fin ∘ suc) p (fsuc a)
  ≡ fsuc (subst Fin p a)
subst-fsuc-reorder = _
```

On the left side of the `≡`, we see a subst applying to `(Fin ∘ suc)`,
whereas on the right side, we see `subst` applied to just `Fin`, this
is required because the path connects naturals, `x ≡ y`, and `a : Fin x`,
but `fsuc a : Fin (suc x)`. This is what `transport-reorder` accounts for. 

```
transport-reorder
  : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {x y : A}
  → (f : A → A) (g : {z : A} → B z → B (f z)) (p : x ≡ y) (a : B x)
  → transport (λ i → B (f (p i))) (g a)
  ≡ g (transport (λ i → B (p i)) a)
```

To implement this, the idea is that we create a two dependent paths, 
that is a path that maps beteen different types across a secondary
'path family'. Each path uses transport-filler to create a
dependent path between both components effectively creating two
triangles (the transport-filler), 'glued' at a the edge `refl {g a}`. This
gives us a dependent path `composite`, where the dependent component,
`λ j → B (f (p (~ j)))` of `step1` is the exact symmetric form of the
dependent component of `step2`, `λ j → B (f (p j))`. This means we can
substitute the dependent component of `composite`, applying the
groupoid cancellation law, to obtain a path with a constant family,
i.e. a simple (non-dependent) path as required.

TODO: Diagram?
```
transport-reorder B f g p a =
  let
    step1 : (λ j → B (f (p (~ j))))
      [ transport (λ i → B (f (p i))) (g a)
      ≡ g a
      ]
    step1 = symP (transport-filler (λ i → B (f (p i))) (g a))
    step2 : (λ j → B (f (p j)))
      [ g a
      ≡ g (transport (λ i → B (p i)) a)
      ]
    step2 = congP (λ i ○ → g ○) (transport-filler (λ i → B (p i)) a)
    composite : (λ i → B ((sym (cong f p) ∙ (cong f p)) i))
      [ transport (λ i → B (f (p i))) (g a)
      ≡ g (transport (λ i → B (p i)) a)
      ]
    composite = compPathP' {B = B} step1 step2
  in
    -- Our path index goes out and back along the same path,
    -- so contract that to a point to give a non-dependent path.
    subst (λ ○ → PathP (λ i → B (○ i))
                 (transport (λ i → B (f (p i))) (g a))
                 (g (transport (λ i → B (p i)) a)))
          (lCancel (cong f p)) composite

-- Synonym for transport-reorder
subst-reorder
  : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {x y : A}
  → (f : A → A) (g : {z : A} → B z → B (f z)) (p : x ≡ y) (a : B x)
  → subst B (cong f p) (g a)
  ≡ g (subst B p a)
subst-reorder B f g p a = transport-reorder B f g p a
```

We then apply the above construction to the subst2 case, where there
are two simultaneous substiution paths. This can't use the above
approach directly, because dependent paths only have a single path as
their family. Instead we construct the path family to be the product
of the two substitution paths `p`, `q`, but the overall idea is the
same as `transport-reorder`.
```
subst2-reorder
  : ∀ {ℓ ℓ'} {A A' : Type ℓ}
    (B : A → A' → Type ℓ') (B' : A → A' → Type ℓ')
    {x y : A} {w z : A'}
  → (g : {z : A} {z' : A'} → B z z' → B' z z')
  → (p : x ≡ y) (q : w ≡ z) (a : B x w)
  → subst2 B' p q (g a) ≡ g (subst2 B p q a)
subst2-reorder B B' g p q a =
  let
    step1 : (λ j → B' (p (~ j)) (q (~ j)))
      [ transport (λ i → B' (p i) (q i)) (g a) ≡ g a ]
    step1 = symP (transport-filler (λ i → B' (p i) (q i)) (g a))

    step2 : (λ j → B' (p j) (q j))
      [ g a ≡ g (transport (λ i → B (p i) (q i)) a) ]
    step2 = congP (λ i ○ → g ○) (transport-filler (λ i → B (p i) (q i)) a)

    composite : (λ i → B' ((sym p ∙ p) i) ((sym q ∙ q) i))
      [ transport (λ i → B' (p i) (q i)) (g a) ≡ g (transport (λ i → B (p i) (q i)) a) ]
    composite = compPathP' {B = λ x → B' (proj₁ x) (proj₂ x)}
                           step1 step2
  in subst2 (λ ○ □ → PathP (λ i → B' (○ i) (□ i))
                   (transport (λ i → B' (p i) (q i)) (g a))
                   (g (transport (λ i → B (p i) (q i)) a)) )
        (lCancel p) (lCancel q) composite
```

This is the last use of the pattern. This states that a constructor in
some variable `y` is equivalent to constructing in an equivalent value
`x` and then substituting along the path between `x` and `y`. We will
use this for base case constructors such as `fzero`.
```
resubst : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
        → (c : (z : A) → B z)
        → {x y : A} (p : x ≡ y)
        → c y ≡ subst B p (c x)
resubst B c {x = x} {y = y} p =
  let step1 : (λ i → B (p (~ i))) [ c y ≡ c x ]
      step1 i = c (p (~ i))
      step2 : (λ i → B (p i))
            [ c x
            ≡ subst B p (c x)
            ]
      step2 = transport-filler (λ i → B (p i)) (c x)
      composite : (λ i → B ((sym p ∙ p) i))
        [ c y
        ≡ subst B p (c x)
        ]
      composite = compPathP' {B = B} step1 step2
  in subst (λ ○ → PathP (λ i → (B (○ i)))
                  (c y)
                  (subst B p (c x)))
           (lCancel p) composite
```

Working with dependent paths directly is difficult and there is
limited support in for path syntax to join depdendent paths
together. This appears to be a limitation of Agda Cubical Library as
well as 1Lab. I spent some time trying to create my own path syntax
for `compPathP'`, but it would result in either unsolved metas, or
syntax requiring so many additional arguments, that it wasn't worth
using. It is unclear to me whether this is a limitation of Cubical
Agda itself, or whether an additional function could be added to the
library to add ergonomics with depdendent paths. My apprach has been
to avoid them as much as possible.

## Properties of Sum Types

A (simple) sum type is another name for a disjoint union, or tagged
union. It is denoted in Agda as `⊎`, with constructors `inl` and `inr`
for the 'left' and 'right' parts of the union, respectively. There are
a few lemmas missing in the Agda Cubical library; we prove them here.

This first lemma states that the two sides of the set are disjoint. We
do this using a predicate `P` and `subst` to construct an element of `⊥`:
```
inl≢inr : {A B : Type} → (a : A) → (b : B) → inl a ≢ inr b
inl≢inr {A} {B} a b p = subst P p tt
  where
    P : A ⊎ B → Type
    P (inl _) = ⊤
    P (inr _) = ⊥
```

We can apply a similar trick to the above to prove injectivity for
both `inl` and `inr`. (Provided by Naïm Camille Favier at https://agda.zulipchat.com/#narrow/channel/260790-cubical/topic/.E2.9C.94.20Splitting.20an.20interval.20in.20Agda.20Cubical).
The idea is that we want to have a predictate that produces a path
from `x` to the argument provided, in the `inl` case. Start with `refl
{inl x}`, and `subst` the endpoint along the path `p` to `inl y`. This
results in a path in `x ≡ y` as required. Note that the `inr` case is impossible, and only used for type-checking the predicate.
```
inl-injective : {A B : Type} (x y : A) → inl x ≡ inl y → x ≡ y
inl-injective {A} {B} x y p = subst P p refl
  where
    P : A ⊎ B → Type
    P (inl a) = x ≡ a
    P (inr b) = ⊥

inr-injective : {A B : Type} (x y : B) → inr x ≡ inr y → x ≡ y
inr-injective {A} {B} x y p = subst P p refl
  where
    P : A ⊎ B → Type
    P (inl a) = ⊥
    P (inr b) = x ≡ b
```

This lemma states that if you have ⊎-map (which takes two functions
that act on the left and right), on two identity functions, then the
overall effect is the same as identity. This just comes down to using
function extensionality, the notion that a pair of functions are equal
if they produce the same outputs given the same inputs. Our proof that these two functions are exetnsionally equal is given as `e`, which is straight-forward.
```
⊎-map-id≡id : {A B : Type} → ⊎-map (id {A = A}) (id {A = B}) ≡ id
⊎-map-id≡id {A = A} {B} = funExt e
  where
    e : (x : A ⊎ B) → ⊎-map id id x ≡ id x
    e (inl x) = refl
    e (inr x) = refl
```

The same trick as above is applied to `⊎-map-∘`, which is a function
that lets us say the that composition of two `⊎-map` pairs is the same
as a single ⊎-map of the composition.
```
⊎-map-∘ : {A A' A'' B B' B'' : Type}
        → (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
        → ⊎-map f' g' ∘ ⊎-map f g ≡ ⊎-map (f' ∘ f) (g' ∘ g)
⊎-map-∘ f f' g g' = funExt e
  where
    e : (x : _) →
         (⊎-map f' g' ∘ ⊎-map f g) x ≡ ⊎-map (f' ∘ f) (g' ∘ g) x
    e (inl x) = refl
    e (inr x) = refl
```

Finally for this section, we define the simple lemma that states that
if `mapMaybe` results in `nothing` then the input must have been
`nothing`.
```
mapMaybeNothing : ∀ {A B : Type} → {x : Maybe A} {f : A → B}
                → map-Maybe f x ≡ nothing → x ≡ nothing
mapMaybeNothing {x = nothing} map≡∅ = refl
mapMaybeNothing {x = just x} map≡∅ = absurd (¬just≡nothing map≡∅)
```
