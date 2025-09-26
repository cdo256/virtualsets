<!--
```
module Dissertation.TransformInjCompose where

open import Cubical.Data.List.Base hiding ([_])
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Prod.Base hiding (map)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base hiding (idInj)
open import VSet.Prelude hiding (id)
open import VSet.Transform.Inj.Elementary.Base
open import VSet.Transform.Inj.Inverse.Insert

private
  variable
    k l m n k' l' m' n' : ℕ
```
-->

## Composition

From here we can define compose inductively, by seeing where each edge
ends up under composition. `b ≡ apply (inc b f) f0`, so
`apply (g ∘ʲʲ inc b f) f0 ≡ apply g b`, therefore the first link should
be from f0 to `apply g b`. We then remove the link from the
composition and recurse.

```
_∘ʲ_ : ∀ {l m n} (g : Inj m n) (f : Inj l m) → Inj l n
g ∘ʲ (nul _) = nul _
_∘ʲ_ {suc l} {suc m} {suc n} g (inc b f) = inc (apply g b) (remove b g ∘ʲ f)
```

If there is at least one edge, then it recurses on the first edge of
the first funciton, tracing where it is applied to, then recursing on
the composition of removing that edge from both graphs.

We want this resulting graph to respect the compatability of
application with composition.

```latex
\begin{lemma}[\texttt{apply-apply}]
```

Given `f : Inj l m`, `g : Inj m n` then applying the composition
should give you the same thing as applying them in sequence:

`(f : Inj l m) (g : Inj m n) (a : ⟦ l ⟧) → apply g (apply f a) ≡ apply (g ∘ʲ f) a`

For all `a : Fin l`.
```latex
\end{lemma}
```

Proof: This is proven in the code in `VSet.Transform.Inj.Compose.Properties`
as `apply-apply`. Although the result appears quite straight-forward
conceptually, this required several sublemmas to prove, and a few
hundred lines of Agda to formalize.
We proceed by induction. In the `a = fzero` case, it is immediate from
the definition of composition that `apply (g ∘ʲ inc b f) fzero ≡ apply g b`.
The inductive case comes down to showing by equational reasoning that
`apply g (fsplice b (apply f a)) ≡ fsplice (apply g b) (apply (remove b g ∘ʲʲ f) a)`.
This is a non-trivial result, and is quite intricate.

```latex
\begin{lemma}[\texttt{∘ʲ} is Assiciative]
```
For all `f : Inj k l`, g : Inj l m, h : Inj m n`,

Then `h ∘ʲ (g ∘ʲ f) ≡ (h ∘ʲ g) ∘ʲ f`
```latex
\end{lemma}
```

We make use of extensionality that `∀ x → apply f x ≡ apply g x`, then `f ≡ g`.

Going back to associativity, it essentially comes down to showing

`∀ x → apply (h ∘ʲ (g ∘ʲ f)) x ≡ apply ((h ∘ʲ g) ∘ʲ f) x`

which comes from repeatedly using `apply-apply` from both sides until the form below is reached. `∎`

## `Inj` Category Construction

Recall that a category is a mathematical structure that can be thought
of as a directed grap with a certain composition on the edges (called
morphisms) that is associative, and that each node (called objects)
have an arrow from themselves to themselves that acts as an identity.

One of the goals of the project is to construct a category of
injective functions on finite sets. If we choose to pick a canonical
finite set for each cardinality, as we have been doing, then the
objects of the category can be indexed by `ℕ` so we pick `ℕ` to be the
set of objects. For morphisms we want injective functions, so we pick
our inductive representation `Inj`. Now the rest is fairly straight-forward:
 - Composition is `_∘ʲ_`.
 - Identity morphisms are the identity inj functions.
```
idInjׅ : ∀ {m} → Inj m m
idInjׅ {zero} = nul zero
idInjׅ {suc m} = inc fzero (idInjׅ {m})
```
We have just proven that `_∘ʲ_` is associative, so we just need to
check that `idInj` is a left and right identity, which follows from
function extensionality, using `apply-apply`, and using the fact that
`idInj` does in fact act as an identity function:

These are given by `∘ʲ-idR` and `∘ʲ-idL` for right and left identity
respectively.

The final requirement is a peculuar feature of homotopy type theory,
where we want to know that the types of arrows from one object to
another (i.e., `Inj m n` for some `m n : ℕ`) have to be *sets*,
meaning they have no deeper homotopic structure than mere identity of
morphisms. Formally, the type of equalities between any two morphisms
is a *proposition*.

```latex
\begin{definition}[Set]
\label{def:set}
```
In homotopy type theory, a type $X$ is a set if for every pair of
elements $a, b ∈ X$, we have that their equality type `a ≡ b` is a
proposition (defined below).
```latex
\end{definition}
```

```latex
\begin{definition}[Proposition]
\label{def:prop}
```
A type $X$ is a *proposition* if, for every pair of inhabitents $a, b ∈ X$, we have that `a ≡ b` is inhabited.
```latex
\end{definition}
```

```latex
\begin{lemma}\label{lem:inj-is-set}
```
For every $n, m ∈ ℕ$, we have that `Inj m n` is a set.
```latex
\end{lemma}
```
This result is given by `isSetInj` in `VSet.Data.Inj.Order`.

<!--
```
open import VSet.Prelude hiding (id)
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Compose.Properties
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties
open import VSet.Data.Inj.Base using (idInj)
```
-->
```
open Category

InjCat : Category _ _
InjCat = record
  { ob = ℕ
  ; Hom[_,_] = Inj
  ; id = λ {x} → idInj x
  ; _⋆_ = _∘⁻ʲ_
  ; ⋆IdL = ∘ʲ-idR
  ; ⋆IdR = ∘ʲ-idL
  ; ⋆Assoc = λ x y z → ∘ʲ-assoc z y x
  ; isSetHom = isSetInj
  }
```

```
InjProdCat : Category _ _
InjProdCat = InjCat ×C InjCat
```

```
⊕-ob : InjProdCat .ob → InjCat .ob
⊕-ob (m , n) = m + n

⊕-hom : {x y : InjProdCat .ob} → InjProdCat [ x , y ]
      → InjCat [ ⊕-ob x , ⊕-ob y ]
⊕-hom (f , g) = f ⊕ g

⊕-id : {x : InjProdCat  .ob}
     → ⊕-hom {x = x} {y = x} (InjProdCat .id)
     ≡ InjCat .id {x = ⊕-ob x}
⊕-id {(m , n)} =
  ⊕-hom {x = (m , n)} {y = (m , n)} (InjProdCat .id)
    ≡⟨ refl ⟩
  ⊕-hom {x = (m , n)} {y = (m , n)} (Id , Id)
    ≡⟨ refl ⟩
  Id {m} ⊕ Id {n}
    ≡⟨ Id⊕Id≡Id {m} {n} ⟩
  Id {m + n} ▯

⊕-seq : {x y z : InjProdCat .ob} (f : InjProdCat [ x , y ]) (g : InjProdCat [ y , z ])
      → ⊕-hom (f ⋆⟨ InjProdCat ⟩ g) ≡ (⊕-hom f) ⋆⟨ InjCat ⟩ (⊕-hom g)
⊕-seq {(l , l')} {(m , m')} {(n , n')} (f , f') (g , g') =
  ⊕-hom ((f , f') ⋆⟨ InjProdCat ⟩ (g , g'))
    ≡⟨ {!!} ⟩
  ⊕-hom (f ∘⁻ʲ g , f' ∘⁻ʲ g') 
    ≡⟨ {!!} ⟩
  (f ⊕ f') ∘⁻ʲ (g ⊕ g') ▯

tensorStr : TensorStr InjCat
tensorStr = record
  { ─⊗─ = record
    { F-ob = ⊕-ob
    ; F-hom = ⊕-hom
    ; F-id = ⊕-id
    ; F-seq = ⊕-seq
    }
  ; unit = {!!}
  }
```
