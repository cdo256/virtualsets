<!--
```
module Dissertation.Inj where

open import Cubical.Data.List.Base hiding ([_])
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Prod.Base hiding (map)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Prelude

private
  variable
    m n : ℕ
```
-->

\begin{verbatim}[hide]
module DissertationTex.Inj where

open import Cubical.Data.List.Base hiding ([_])
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Prod.Base hiding (map)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Prelude

private
  variable
    m n : ℕ
\end{verbatim}

## Definition of Inj

I have taken the approach of using a basic inductive definition for injective functions. This was because the previous way of doing it was messy, and ultimately hid the true behaviour that I wanted to extract with a trace. This meant that all of the proofs relied on a long chain of isomorphisms that weren't strong enough to capture the behaviour that we cared about, namely adding and removing links to modify a funciton.

Additionally carrying around the proof meant they had to be modified together, and may have been the reason I was experiencing performance reduction when type checking Agda.

I noticed that I wasn't getting the benefit I expected from all of these abstractions and that ultimately proving these isomorphisms were distracting from the main aim which is ensure that a trace structure is formed from Virtual Sets. I do think this method could have worked if I had enough time, but the problem is that I didn't have the time to spare. Additionally techniques I've learnt made it clear that there were much better ways of structuring things so that . (?)

In the aid of this simplicity, I decided to switch to the following structure to represent injective Fin funcitons:

```
data Inj : ℕ → ℕ → Type where
  nul : ∀ n → Inj 0 n
  inc : ∀ {m n} → (b : Fin (suc n))
      → (inj : Inj m n)
      → Inj (suc m) (suc n)
```

This replaces the previous definition:
```
[_↣_] : ℕ → ℕ → Type
[ X ↣ Y ] = Σ (Fin X → Fin Y) is-injective
```

The way it works is that nul introduces an empty function from `Fin 0` to some `Fin n`. Then each subsequent `inc` adds a single link shifting the domain and codomain such that it is impossible to construct a non-injective function.

I represent these functions as vectors of finite values, where the position corresponds to each domain element, and the number is what that element is mapped to. For example, let's introduce compact notation to represent

$$
  (1\ 2\ 0)
$$

maps 0 to 1, 1 to 2, and 2 to 0. Note that there is some ambiguity with this notation in that we haven't specified the size of the codomain. This can be displayed graphically as in Figure \ref{fig:120}

\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  \dotrow{2}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{2}{a}{below}
  \end{scope}
  \draw (a0) -- (b1);
  \draw (a1) -- (b2);
  \draw (a2) -- (b0);
 \draw[thick,->,>=stealth, line width=2pt] (3,-2) -- ++(0,2);
\end{tikzpicture}
\caption{Plot of $(1\ 2\ 0)$. The bottom row is the domain and the top row is the codomain. The arrow indicates the direction from domain to codomain.}
\label{fig:120}
\end{figure}

Strictly we would want to specify the type to fully specify this. In our notation we would represent this as:

TODO: Increase code font size

```
f : Inj 3 3
f = inc f1 $ inc f1 $ inc f0 $ nul 0
```

TODO: Reword, call 0 the slack.

\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
\begin{scope}[local bounding box=box1]
  \dotrow{0}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{0}{a}{below}
  \end{scope}
  \draw[color=red,ultra thick] (a0) -- (b0);
\end{scope}
\node[below=2mm of box1.south] {inc f0 \$ nul 0};
\begin{scope}[xshift=4cm, local bounding box=box2]
  \dotrow{1}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{1}{a}{below}
  \end{scope}
  \draw[color=red,ultra thick] (a0) -- (b1);
  \draw (a1) -- (b0);
\end{scope}
\node[below=2mm of box2.south] {inc f1 \$ inc f0 \$ nul 0};
\begin{scope}[xshift=9cm, local bounding box=box3]
  \dotrow{2}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{2}{a}{below}
  \end{scope}
  \draw[color=red,ultra thick] (a0) -- (b1);
  \draw (a1) -- (b2);
  \draw (a2) -- (b0);
\end{scope}
\node[below=2mm of box3.south] {inc f1 \$ inc f1 \$ inc f0 \$ nul 0};
  \draw[
    ultra thick,
    -{>[length=8mm, width=8mm]},
    shorten >=1cm,
    shorten <=1cm
    ] (box1.east) -- (box2.west) node[below=5mm, midway] {inc f1};
  \draw[
    ultra thick,
    -{>[length=8mm, width=8mm]},
    shorten >=1cm,
    shorten <=1cm
    ] (box2.east) -- (box3.west) node[below=5mm, midway] {inc f1};
\end{tikzpicture}
\caption{Construction of $(1\ 2\ 0)$ starting from $\mathrm{inc f0 \$ nul 0}$.}
\label{fig:120-construction}
\end{figure}

This is read right to left. First we start with `nul 0` which is an empty function with an empty codomain. The difference between the size of the domain and the codomain is specified entirely by this nul funciton. Starting with `nul 0` means we will end up with a bijection, although this needs to be proven. In a sense, it is the measure of how close to a surjection the funciton is. Since the funciton is injective by construction, we know that the size of the range is equal to the range. So the value given to nul is the difference between the size of the codomain and the domain. This value remains constant as links are added.

Next we add a single link from f0 to f0. This is the only choice we have at this stage because we're creating a function from Fin 1 to Fin 1 from `nul 0 : Fin 0 → Fin 0`.

The second link we add gives us two choices. We can either be parallel to the first link or cross over it. `(inc f0 $ inc f0 $ nul 0)` is two parallel links. `(inc f1 $ inc f0 $ nul 0)` is two crossing links. Note that these are the only two bijections from Fin 2 to Fin 2 available. We choose to cross in this example.

Finally the third link can either cross over both (`f2`), cross over just one (`f1`), or not cross at all (`f0`). We choose the middle option and end up with a cycle. Note that after nul 0, we three choices, 1 \* 2 \* 3 = 3!. Every inc that is added increases the type of the Fin added by 1. Therefore, starting with `nul 0` to make `Inj m m`, there are m! options, which indicates that we're representing all possibilities. (Though it still needs to be checked that there is only one way to construct each function.)

This has the nice properties that all constructions are necessarily injective, since it is impossible to construct two outputs that are the same, for example (0 0) : Fin 2 cannot be constructed. This is because each insertion 'splices the output domain, shifting all links to all codomain elements that are greater than or equal to the new link's codomain element.

### Compositional Definition

## Splice Algebra

The first function that needs to be written for this definition to be usable is `apply`. Specifically from the construction of Inj function, we need to be able to every value from the domain into the codomain. To see how to construct this, suppose we have an `f : Inj m n` with m non-zero. For an example, consider the function,

```
f = inc f3 $ inc f0 $ inc f1 $ inc f0 $ inc f0 $ nul 0
```

This is diagrammed in Figure \ref{fig\:splice-ex-f}.

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
\caption{Plot of \textrm{f = inc f3 \$ inc f0 \$ inc f1 \$ inc f0 \$ inc f0 \$ nul 0}.}
\label{fig:splice-ex-f}
\end{figure}

Now reading $f f0$ is immediate, it's just what the last inserted link associates to. For example, since we have `f ≡ inc f3 _`, we know that the first link we read off is $(0, 3)$. Thus we can fill in that case,

```
apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc b g) fzero = b
```

Write the rest of the function as `g`, which is diagrammed in Figure \ref{fig\:splice-ex-g}. Then `f = inc f3 g`.

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
\caption{Plot of $g = inc f0 \$ inc f1 \$ inc f0 \$ inc f0 \$ nul 0$ (drawn
    suggestively for easier comparison with f).}
\label{fig:splice-ex-g}
\end{figure}

Now to get the successor case, suppose we have $suc n$, we need to recurse on $g$. This gives us the correct values for all outputs that are less than $b$, in our case $f3$. The final operation we need, I call a `fsplice`, one of a family of operations on Fin that provide utilities for operating on Fin types.

`fsplice b` maps `Fin x` to `Fin (suc x)` in such a way that b is not in the codomain. Essentially it increments all values above (or equal to b and keeps the values less than b unchanged. This is visualized in Figure \ref{fig\:fsplice}.

```
fsplice : ∀ {x} → (b : Fin (suc x)) → (a : Fin x) → Fin (suc x)
fsplice fzero a = fsuc a
fsplice (fsuc b) fzero = fzero
fsplice (fsuc b) (fsuc a) = fsuc (fsplice b a)
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
\caption{Plot of \textrm{fsplice 3} on \textrm{x} = 5.}
\label{fig:fsplice}
\end{figure}

`fcross` (see Figure \ref{fig\:fcross}) is in some ways the opposite to `fsplice`. The idea is that given a pivot point `b`, it creates a funciton that `merges' the adjacent codomain elements located at `b`and`b + 1\`.

```
fcross : ∀ {x : ℕ} → (b : Fin x) → (a : Fin (suc x)) → Fin x
fcross fzero fzero = fzero
fcross (fsuc b) fzero = fzero
fcross fzero (fsuc a) = a
fcross (fsuc b) (fsuc a) = fsuc (fcross b a)
```

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
open import VSet.Data.Fin.Order

fjoin-cases : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
                → Trichotomyᶠ a b → Fin x
fjoin-cases b a a≉b (flt a< b) = fin-restrict-< a a< b
fjoin-cases b a a≉b (feq a≈b) = absurd (a≉b a≈b)
fjoin-cases b (fsuc a) a≉b (fgt b< a) = a

fjoin : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
           → Fin x
fjoin b a a≉b = fjoin-cases b a a≉b (a ≟ᶠ b)
```

`fjoin` is like `fcross` but it ensures that the pivot `b` is not in the domain, by taking `a ≉ᶠ b`. This ensure that fjoin and fsplice are exact inverses.

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
  \draw (a4) -- (b3);
  \draw (a5) -- (b4);
\end{tikzpicture}
\caption{Plot of \textrm{fjoin 2} on \textrm{x} = 4. Note that an input value of 3 is not possible}
\label{fig:fjoin}
\end{figure}

These work with an apply function given below.


```
apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc b inj) fzero = b
apply (inc b inj) (fsuc a) =
  fsplice b (apply inj a)
```

```
to-list : Inj m n → List (Fin n)
to-list (nul _) = []
to-list (inc b f) =
  b ∷ map (fsplice b) (to-list f)
```

```
_∈ʲ_ : ∀ {n m : ℕ} → (b : Fin n) → (Inj m n) → Type
b ∈ʲ f = Σ[ a ∈ Fin _ ] apply f a ≡ b
```

```
_∉ʲ_ : ∀ {n m : ℕ} → (b : Fin n) → (Inj m n) → Type
b ∉ʲ f = ¬ b ∈ʲ f
```

```
idInj : ∀ m → Inj m m
idInj zero = nul zero
idInj (suc m) = inc fzero (idInj m)
```

```
-- Alternate name
𝟙 : ∀ {m} → Inj m m
𝟙 {m} = idInj m
```

```
𝟙-isId : ∀ m → (a : Fin m) → apply (𝟙 {m}) a ≡ a
𝟙-isId m fzero = refl
𝟙-isId (suc m) (fsuc a) = cong fsuc (𝟙-isId m a)
```

```
cross : Inj 2 2
cross = inc (fsuc fzero) $ inc fzero $ nul 0
```

```
-- eg. cycle-l 5 = (5 0 1 2 3 4)
cycle-l : ∀ m → Inj (suc m) (suc m)
cycle-l m = inc fmax (idInj m)
```

```
-- eg. cycle-r 5 = (1 2 3 4 5 0)
cycle-r : ∀ m → Inj (suc m) (suc m)
cycle-r zero = idInj 1
cycle-r (suc m) = inc (fsuc fzero) (cycle-r m)
```

```
injExt : ∀ {m n} → (f g : Inj m n)
       → (∀ x → apply f x ≡ apply g x) → f ≡ g
injExt (nul _) (nul _) _ = refl
injExt (inc b f) (inc c g) f'x≡g'x =
  inc b f
    ≡⟨ cong (λ ○ → inc ○ f) (f'x≡g'x f0) ⟩
  inc c f
    ≡⟨ cong (inc c) f≡g ⟩
  inc c g ▯
  where
    fx≡gx : ∀ x → apply f x ≡ apply g x
    fx≡gx x =
      apply f x
        ≡⟨ (fsplice-isInjective
          ((f'x≡g'x (fsuc x))
          ∙ sym (cong (λ ○ → fsplice ○ (apply g x)) (f'x≡g'x f0)))) ⟩
      apply g x ▯
    f≡g : f ≡ g
    f≡g = injExt f g fx≡gx
```
