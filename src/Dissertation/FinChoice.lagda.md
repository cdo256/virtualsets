<!--
```
module Dissertation.FinChoice where
open import VSet.Prelude
open import VSet.Function.Iso
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin hiding (fzero; fsuc)
open import Compat.1Lab.Data.Fin renaming (Fin to Fin′)
open import Compat.1Lab.Data.Irr
open import Cubical.Data.Sum
```
-->

# Choice of Finite Set Representation

*This section is a modification of an email I sent to Thorsten
Altenkirch and Mark Williams on 30th June 2025.*

In this project, finite sets have initially been defined in terms of
the inductive type `Fin`. However, this representation does not carry
over cleanly to cubical Agda. While the 1Lab library provides some
support, it is considerably less developed than Agda’s cubical
library. Time was therefore spent transferring definitions from the
1Lab library to Agda cubical.

An important theorem that we want to prove is the equivalence of two ways
of composing finite sets,

```
+≅⊎ : ∀ {x y} → Fin x ⊎ Fin y ≅ Fin (x + y)
+≅⊎ = _
```

Progress has been made up to Lemma 1.3. However, difficulties arose in
the definition of `+→⊎`, where the use of a `with` clause obscured
information required for type checking. This caused proof complexity
to grow substantially. To address the issue, `+≅⊎` was redefined, but
this in turn lead to obstacles in proving the following property:

```
ℕ≡→Fin≡ : ∀ {x : ℕ} (a b : Fin′ x) → Fin′.lower a ≡ Fin′.lower b → a ≡ b
ℕ≡→Fin≡ {x} a b lowerEq = {!!}
```

The difficulty reduces to showing,

```
irr-subst : ∀ (a x y : ℕ) → (ix : Irr (a < x)) → (iy : Irr (a < y))
          → x ≡ y → {!ix ≡ iy!}
irr-subst = {!!}
```

Here, the central challenge lies in the fact that `ix` and `iy` are
considered to have different types, which prevents even the statement
of the goal. One potential direction is to employ the dependent form
of `ap`, namely `apd`:

```
apd : ∀ {a b} {A : I → Type a} {B : (i : I) → A i → Type b}
    → (f : ∀ i (a : A i) → B i a) {x : A i0} {y : A i1}
    → (p : PathP A x y)
    → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
apd f p i = f i (p i)
```

At present, the use of `apd` does not seem natural, which likely
reflects a lack of experience reasoning in explicitly homotopical
terms. To address this, time was taken to review the HoTT book and
Robert Harper’s lecture series on homotopy type theory. CITE

It is worth noting that the analogous property is trivial to prove
when `x` and `y` are of the same type, which suggests that the
difficulty does not lie with `Irr` itself:

```
irr-is-prop : (X : Type) → (x y : Irr X) → x ≡ y
irr-is-prop X a b = refl
```

An advantage of 1Lab is that categories are defined cubically, without
resorting to setoids. While this may become a limitation in later
stages, its impact remains to be seen. It would in principle be
possible to contribute additional material back to 1Lab, but this was
agreed to be a distraction from the aims project in the available time.

The cubical library offers a broader range of definitions for `Fin`
and more utilities for working with them. Consequently, the natural
strategy is to commit to one definition of `Fin` that proves most
convenient. At the time of writing, I had proven a few basic
properties about virtual sets using the Agda standard library. The
results have been partially ported to 1Lab, but it appears that
porting instead to the cubical library would require a
similar level of effort. The main difficulty with 1Lab lies in its
particular definition of `Fin`, which complicates reasoning. Several
alternatives are available:

```
-- Indexed inductive type
-- From agda-stdlib
private
  variable n : ℕ
data Fin₁ : ℕ → Type where
  fzero : Fin₁ (suc n)
  fsuc  : (i : Fin n) → Fin₁ (suc n)

-- Bounded naturals (with irrelevant proof)
-- From 1lab
record Fin₂ (n : ℕ) : Type where
  constructor fin
  field
    lower       : ℕ
    ⦃ bounded ⦄ : Irr (lower < n)

-- Agda Cubical main definition
Fin₃ : ℕ → Type
Fin₃ n = Σ[ k ∈ ℕ ] k < n

-- Alternative definition in Agda Cubical
Fin₄ : ℕ → Type
Fin₄ zero = ⊥
Fin₄ (suc n) = ⊤ ⊎ (Fin n)

-- Agda Cubical main except that <ᵗ is defined by computing the
-- trichotomy of two integers, and is either ⊤ or ⊥, making it
-- propositional.
_<ᵗ_ : (n m : ℕ) → Type
n <ᵗ zero = ⊥
zero <ᵗ suc m = ⊤
suc n <ᵗ suc m = n <ᵗ m


Fin₅ : ℕ → Type
Fin₅ n = Σ[ k ∈ ℕ ] k <ᵗ n
```

Although it would be possible to define an indexed inductive type in
the familiar style, a comment in the cubical library explicitly
advises against this approach:

```
-- Currently it is most convenient to define these as a subtype of the
-- natural numbers, because indexed inductive definitions don't behave
-- well with cubical Agda. This definition also has some more general
-- attractive properties, of course, such as easy conversion back to
-- ℕ.
```

This discourages redefining `Fin` in the traditional way. Instead, the
trichotomous definition appears to offer the cleanest solution, since
propositionality suffices for the purposes of this work. There is no
need to track *how* `i < x` holds, only that it does.

In light of this, it seems preferable to transition to the standard
cubical library at an early stage in the project. While this involved
rewriting a substantial portion of the work completed so far, much of the
necessary material already exists in the cubical library. The
remaining work of porting was relatively straightforward. Before
beginning this process, I took some time to familiarise fully with
the cubical library’s definitions to avoid reimplementing existing
lemmas.
