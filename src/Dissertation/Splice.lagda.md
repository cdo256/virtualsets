<!--
```
module Dissertation.Splice where

open import Cubical.Data.Maybe
open import Cubical.Data.Nat
  using (ℕ; _+_; +-zero; +-suc; zero; suc;
        +-assoc; +-comm)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Minus
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
  using (fzero≡subst-fzero;
         subst-fsuc-reorder;
         finject-fsuc-reorder;
         finject0≡subst;
         ≉fsuc )
open import VSet.Data.Nat.Order
open import VSet.Data.Inj.Base hiding (apply)
open import VSet.Data.Nat.Properties
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Prelude

private
  variable
    ℓ : Level
    x y z : ℕ
    a : Fin x
    b : Fin y
```
-->


## 'Splice' operations on \texttt{\large Fin} {#splice-operations-on-fin}

In the definition of `Inj`, we have taken the approach of using a
basic inductive definition for injective functions. This was because
the dependent sum representation (`InjFun`) of doing it was messy, and
ultimately hid the true behaviour that I wanted to extract with a
trace. This meant that all of the proofs relied on a long chain of
isomorphisms that weren't strong enough to capture the behaviour that
we cared about, namely adding and removing links to modify a funciton.

Additionally carrying around the proof meant they had to be modified
together, and may have been the reason I was experiencing performance
reduction when type checking Agda.

I noticed that I wasn't getting the benefit I expected from all of
these abstractions and that ultimately proved these isomorphisms were
distracting from the main aim which is ensure that a trace structure
is formed from Virtual Sets. I do think this method could have worked
if I had enough time, but the problem is that I didn't have the time
to spare.

The first function that needs to be written for this definition to be
usable is `apply`. Specifically from the construction of Inj function,
we need to be able to every value from the domain into the
codomain. To see how to construct this, suppose we have an `f : Inj m n`
with m non-zero. For an example, consider the function,

```
f = inc f3 $ inc f0 $ inc f1 $ inc f0 $ inc f0 $ nul 0
```

This is diagrammed in Figure \ref{fig:splice-ex-f}.

\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  \dotrow{4}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{4}{a}{below}
  \end{scope}
  \draw (a0) -- (b3);
  \draw (a1) -- (b0);
  \draw (a2) -- (b2);
  \draw (a3) -- (b1);
  \draw (a4) -- (b4);
\end{tikzpicture}
\caption{Plot of \texttt{f = inc f3 \$ inc f0 \$ inc f1 \$ inc f0 \$ inc f0 \$ nul 0}.}
\label{fig:splice-ex-f}
\end{figure}

For the `fzero` case, notice that `f f0` can just be read of as the
target of the last inserted edge, it's just what the last inserted
link associates to. For example, since we have `f ≡ inc f3 _`, we know
that
the first link we read off is $(0, 3)$. Thus we can fill in that case,

```
apply : ∀ {m n} → Inj m n → Fin m → Fin n
```

Let `g` stand for the the remainder of function (with `inc f3 $`
removed), which is diagrammed suggestively for easier comparison with
f in figure \ref{fig:splice-ex-g}. Then by construction, we have `f = inc f3 g`.

\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
    \begin{scope}[start chain=going right]
      \foreach \i in {0,...,2}
        \node[on chain, dotnode, label=above:{\i}] (b\i) {};
      \node[on chain, xshift=1cm, dotnode, label=above:3] (b3) {};
    \end{scope}
  \begin{scope}[yshift=-2cm,xshift=1cm]
    \dotrow{3}{a}{below}
  \end{scope}
  \draw (a0) -- (b0);
  \draw (a1) -- (b2);
  \draw (a2) -- (b1);
  \draw (a3) -- (b3);
\end{tikzpicture}
\caption{Plot of \texttt{g = inc f0 \$ inc f1 \$ inc f0 \$ inc f0 \$ nul 0}.}
\label{fig:splice-ex-g}
\end{figure}

`fsplice b` maps `Fin x` to `Fin (suc x)` in such a way that `b` is not
in the codomain. Essentially it increments all values equal or greater
than b, keeping the values less than `b` unchanged. This is visualized in
Figure \ref{fig:fsplice}. and defined below:
```
fsplice : ∀ {x} → Fin (suc x) → Fin x → Fin (suc x)
fsplice fzero a = fsuc a
fsplice (fsuc b) fzero = fzero
fsplice (fsuc b) (fsuc a) = fsuc (fsplice b a)
```

We call the first argument the 'pivot'. It is necessarily true that
`fsplice b a ≢ a`, which we show below. We will use this to recurse in
the definition of apply. The base case just reads off the target,
which is the first `inc` expanded. The second case, recurses on `g`,
and then uses the splice to ensure there is space for `b` in the
codomain. This is what ensures that all `Inj` functions are injective,
since it's not possible for fsplice to map an element to the pivot:

```
fsplice≉b : ∀ {x} → (b : Fin (suc x)) → (a : Fin x) → fsplice b a ≉ᶠ b
fsplice≉b fzero a = fsuc≉fzero
fsplice≉b (fsuc b) fzero = fzero≉fsuc
fsplice≉b (fsuc b) (fsuc a) ne = 
  let rec≉b = fsplice≉b b a
  in rec≉b (≈fsuc-injective ne)
```

We now have what we need to finish `apply`. To get the successor
case, suppose we have `suc n`, we need to recurse on `g`. This gives
us the correct values for all outputs that are less than `b`, in this
case `f3`. The final operation we need, we call a `fsplice`, one of a
family of operations on Fin that provide utilities for operating on
Fin types. Putting that together we obtain:

```
apply (inc b g) fzero = b
apply (inc b g) (fsuc a) = fsplice b (apply g a)
```

\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  \begin{scope}
    \dotrow{6}{b}{above}
  \end{scope}
  \begin{scope}[yshift=-2cm,xshift=5mm]
    \dotrow{5}{a}{below}
  \end{scope}
  \draw (a0) -- (b0);
  \draw (a1) -- (b1);
  \draw (a2) -- (b2);
  \draw (a3) -- (b4);
  \draw (a4) -- (b5);
  \draw (a5) -- (b6);
\end{tikzpicture}
\caption{Plot of \texttt{fsplice 3} on \texttt{x} = 5.}
\label{fig:fsplice}
\end{figure}

Next we define a function `fcross` (see Figure \ref{fig:fcross}). is
in some ways the opposite to `fsplice`. The idea is that given a pivot
point `b`, it creates a funciton that `merges' the adjacent domain
elements located at `b`and `b + 1`. This is useful when you want to
swap the order of insertion of two values, the one moving out expands
its domain by one and the pivot location encodes the relative order of
two values. While the one moving further into the structure 'loses'
information about the order of the two values.

\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  \begin{scope}
    \dotrow{4}{b}{above}
  \end{scope}
  \begin{scope}[yshift=-2cm,xshift=-5mm]
    \dotrow{5}{a}{below}
  \end{scope}
  \draw (a0) -- (b0);
  \draw (a1) -- (b1);
  \draw (a2) -- (b2);
  \draw (a3) -- (b2);
  \draw (a4) -- (b3);
  \draw (a5) -- (b4);
\end{tikzpicture}
\caption{Plot of \textrm{fcross 2} on \textrm{x} = 4.}
\label{fig:fcross}
\end{figure}

```
fcross : ∀ {x : ℕ} → (b : Fin x) → (a : Fin (suc x)) → Fin x
fcross fzero fzero = fzero
fcross (fsuc b) fzero = fzero
fcross fzero (fsuc a) = a
fcross (fsuc b) (fsuc a) = fsuc (fcross b a)
```

<!--
```
fcross₂ : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
            → Fin (suc x)
fcross₂ _ fzero = fzero
fcross₂ fzero (fsuc a) = a
fcross₂ {suc x} (fsuc b) (fsuc a) =
  fsuc (fcross₂ b a)
```

```
fcross'-cases
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
  → Dichotomyᶠ a b
  → Fin (suc x)
fcross'-cases b a (fle a≤b) = fin-restrict-≤ a a≤b
fcross'-cases b a (fgt a>b) = pred a
```

```
fcross' : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
        → Fin (suc x)
fcross' b a = fcross'-cases b a (a ≤?ᶠ b)
```
-->

The last major operation is called `fjoin`. The idea is that a join is
exactly the opposite to `fsplice`. This will be used to construct an
inverse of function. We implement by making use of 'trichotomy' on the
pivot 'b' with the assumption that the input is distinct from the
pivot. Then if `a` is less than the pivot, we restrict the domain with
`fin-restrict-<` but keep the value unchanged, and if it's larger, we
decrease it by one. It is split up into two functions for ease of
working with `fjoin`. If the function was part of a `where` clause then
it would be inaccessible outside the function, and if it were split on
a `with` clause then it acts the same as a where clause, creating an
inaccessible funciton. This is a limitation of the current version of Agda.

```
fjoin-cases : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
                → Trichotomyᶠ a b → Fin x
fjoin-cases b a a≉b (flt a<b) = fin-restrict-< a a<b
fjoin-cases b a a≉b (feq a≈b) = absurd (a≉b a≈b)
fjoin-cases b (fsuc a) a≉b (fgt b<a) = a

fjoin : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
           → Fin x
fjoin b a a≉b = fjoin-cases b a a≉b (a ≟ᶠ b)
```

<!--
```
-- Another alternate definition
fjoinMaybe
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc x))
  → Maybe (Fin x)
fjoinMaybe fzero fzero = nothing
fjoinMaybe {suc x} fzero (fsuc a) = just a
fjoinMaybe {suc x} (fsuc b) fzero = just fzero
fjoinMaybe {suc x} (fsuc b) (fsuc a) =
  map-Maybe fsuc (fjoinMaybe b a)
```

```
-- Another alternate definition
fjoinMaybe'
  : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x)))
  → Maybe (Fin (suc x))
fjoinMaybe' b a with a ≟ᶠ b
... | flt a<b = just (fin-restrict-< a a<b)
... | feq a≡b = nothing
... | fgt b<a = just (pred a)
```

```
fcross≡fcross'
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
  → fcross b a ≡ fcross' b a
fcross≡fcross' fzero fzero = refl
fcross≡fcross' fzero (fsuc a) = refl
fcross≡fcross' (fsuc b) fzero = refl
fcross≡fcross' {x = suc x} (fsuc b) (fsuc a) with a ≤?ᶠ b 
... | fle a≤b =
  fcross (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (fcross b a)
    ≡⟨ cong fsuc (fcross≡fcross' b a) ⟩
  fsuc (fcross'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ fcross'-cases b a) (isPropDichotomyᶠ (a ≤?ᶠ b) (fle a≤b)) ⟩
  fsuc (fcross'-cases b a (fle a≤b))
    ≡⟨ refl ⟩
  fsuc (fin-restrict-≤ a a≤b)
    ≡⟨ refl ⟩
  fsuc (fin-restrict-< a (≤ᶠ→<ᶠ a≤b))
    ≡⟨ cong (fin-restrict-< (fsuc a)) (sym (fsuc≤fsuc→<fsuc a≤b) ) ⟩
  fin-restrict-< (fsuc a) (≤ᶠ→<ᶠ (fsuc≤fsuc a≤b))
    ≡⟨ refl ⟩
  fin-restrict-≤ (fsuc a) (fsuc≤fsuc a≤b)
    ≡⟨ refl ⟩
  fcross'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fle a≤b))
    ≡⟨ cong (fcross'-cases (fsuc b) (fsuc a))
            (isPropDichotomyᶠ (≤?ᶠ-suc (fle a≤b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  fcross'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
... | fgt a>b =
  fcross (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (fcross b a)
    ≡⟨ cong fsuc (fcross≡fcross' b a) ⟩
  fsuc (fcross'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ fcross'-cases b a) (isPropDichotomyᶠ (a ≤?ᶠ b) (fgt a>b)) ⟩
  fsuc (fcross'-cases b a (fgt a>b))
    ≡⟨ refl ⟩
  fsuc (pred a)
    ≡⟨ fsuc∘pred≡id {y = 1} (≉fsym (<ᶠ→≉ (≤<ᶠ-trans (fzero≤a b) a>b))) ⟩
  a
    ≡⟨ refl ⟩
  fcross'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fgt a>b))
    ≡⟨ cong (fcross'-cases (fsuc b) (fsuc a))
            (isPropDichotomyᶠ (≤?ᶠ-suc (fgt a>b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  fcross'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
open Iso
```

```
fsuc-fjoin 
  : ∀ {x : ℕ} → (b a : Fin (suc x)) → (a≉b : a ≉ᶠ b)
  → fjoin (fsuc b) (fsuc a) (≉fsuc a≉b)
  ≡ fsuc (fjoin b a a≉b)
fsuc-fjoin b        a a≉b with (a ≟ᶠ b)
fsuc-fjoin b        a a≉b | flt a<b = refl
fsuc-fjoin b        a a≉b | feq a≈b = absurd (a≉b a≈b)
fsuc-fjoin b (fsuc a) a≉b | fgt a>b = refl
```

```
fjoin-irrelevant
  : ∀ {x : ℕ} → (b a : Fin (suc x))
  → (u v : a ≉ᶠ b)
  → fjoin b a u ≡ fjoin b a v
fjoin-irrelevant b        a u v with (a ≟ᶠ b)
fjoin-irrelevant b        a u v | flt a<b = refl
fjoin-irrelevant b        a u v | feq a≈b = absurd (u a≈b)
fjoin-irrelevant b (fsuc a) u v | fgt a>b = refl
```

```
fjoin-cong
  : ∀ {x} → {b1 b2 a1 a2 : Fin (suc x)}
  → (p : b1 ≡ b2) → (q : a1 ≡ a2)
  → (ne : a1 ≉ᶠ b1)
  → fjoin b1 a1 ne ≡ fjoin b2 a2 (subst2 _≉ᶠ_ q p ne)
fjoin-cong {b1 = b1} {b2} {a1} {a2} p q ne i =
  fjoin (p i) (q i) (subst2-filler _≉ᶠ_ q p ne i)
```

```
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
```

```
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
```

```
>→fsplice≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → finj a1 <ᶠ a2 → fsplice a2 a1 ≈ᶠ finj a1
>→fsplice≈id fzero (fsuc a2) a1<a2 = ≈refl
>→fsplice≈id {suc m} (fsuc a1) (fsuc a2) a1<a2 =
  ≈fsuc (>→fsplice≈id a1 a2 (<ᶠ-respects-pred a1<a2))
```

```
<→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 <ᶠ a1 → fcross a1 a2 ≈ᶠ a2
<→fcross≈id (fsuc a1) fzero a2<a1 = ≈fzero
<→fcross≈id {suc m} (fsuc a1) (fsuc a2) (<fsuc a2<a1) =
  ≈fsuc (<→fcross≈id a1 a2 a2<a1)
```

```
≈→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≈ᶠ a1 → fcross a1 a2 ≈ᶠ a2
≈→fcross≈id fzero fzero _ = ≈fzero
≈→fcross≈id (fsuc a1) fzero _ = ≈fzero
≈→fcross≈id fzero (fsuc a2) a2'≈0 = absurd (fsuc≉fzero a2'≈0)
≈→fcross≈id {suc m} (fsuc a1) (fsuc a2) a2≈a1 =
  ≈fsuc (≈→fcross≈id a1 a2 (≈fsuc-injective a2≈a1))
```

```
≤→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≤ᶠ a1 → fcross a1 a2 ≈ᶠ a2
≤→fcross≈id a1 a2 (inl a2<a1) = <→fcross≈id a1 a2 a2<a1
≤→fcross≈id a1 a2 (inr a2≈a1) = ≈→fcross≈id a1 a2 a2≈a1
```

```
>→fcross≈pred : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                  → finj a1 <ᶠ a2 → fcross a1 a2 ≈ᶠ pred a2
>→fcross≈pred fzero (fsuc a2) a2>a1 = ≈refl
>→fcross≈pred {suc m} (fsuc a1) (fsuc (fsuc a2)) (<fsuc a2>a1) =
  ≈fsuc (>→fcross≈pred a1 (fsuc a2) a2>a1)
```

```
finj∘fsuc≈fsuc∘finj : ∀ {x} (a : Fin (suc x)) → finj (fsuc a) ≈ᶠ fsuc (finj a)
finj∘fsuc≈fsuc∘finj a = ≈refl
```

```
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
```

```
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
```

```
fin-restrict-<-a≈a
  : ∀ {x} {b : Fin (suc x)} (a : Fin y)
  → (a<b : a <ᶠ b) → fin-restrict-< a a<b ≈ᶠ a
fin-restrict-<-a≈a {x = suc x} fzero <fzero = ≈fzero
fin-restrict-<-a≈a {x = suc x} (fsuc a) (<fsuc a<b) =
  ≈fsuc (fin-restrict-<-a≈a a a<b)
```
-->

```
fcross0≡0 : ∀ {m} → (a : Fin (suc m))
          → fcross a fzero ≡ fzero
fcross0≡0 fzero = refl
fcross0≡0 (fsuc a) = refl
```

```
fcross0s≡pred : ∀ {m} → (a : Fin (suc m))
              → fcross f0 (fsuc a) ≡ a
fcross0s≡pred a = refl
```

```
fcross-fcross-fsplice
  : ∀ {m} → (b : Fin (suc (suc m))) (c : Fin (suc m))
  → (fcross (fcross c b) (fsplice b c)) ≡ c
fcross-fcross-fsplice fzero fzero = refl
fcross-fcross-fsplice fzero (fsuc c) = refl
fcross-fcross-fsplice (fsuc b) fzero = fcross0≡0 b
fcross-fcross-fsplice {m = suc m} (fsuc b) (fsuc c) =
  cong fsuc (fcross-fcross-fsplice b c)
```

<!--
```
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
```

```
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
```

```
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
```
-->

A key lemma is the injectivity of fjoin. The proof is non-trivial
requiring significant pattern matching. This is a general limitation I have found with this approach compared with the `InjFun` approach.

```
fjoin-isInjective
  : {n : ℕ} → (a b c : Fin (suc n))
  → (b≉a : b ≉ᶠ a) → (c≉a : c ≉ᶠ a)
  → fjoin a b b≉a ≡ fjoin a c c≉a → b ≡ c
```

<!--
```
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
```
