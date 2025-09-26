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
open import VSet.Function.Injection
open import VSet.Prelude

private
  variable
    m n : ℕ
```
-->

# \texttt{\large Inj} Representation {#inj-representation}

This section documents the construction of injective functions on
finite sets using an inductive approach. This contrasts the `InjFun`
representation from section \ref{injfun-representation} that uses a
depdendent sum of a function and its proof of injectivity. Below we
will define `Inj` and build up from basic operations on `Fin` up to a
trace operator.

## Definition of \texttt{\large Inj} {#definition-of-inj}

I have taken the approach of using a basic inductive definition for
injective functions. This was because the previous way of doing it was
messy, and ultimately hid the true behaviour that I wanted to extract
with a trace. This meant that all of the proofs relied on a long chain
of isomorphisms that weren't strong enough to capture the behaviour
that we cared about, namely adding and removing links to modify a
funciton to build a trace.

Additionally carrying around the proof meant they had to be modified
together, and may have been the reason I was experiencing performance
reduction when type checking Agda.

I noticed that I wasn't getting the benefit I expected from all of
these abstractions and that ultimately proving these isomorphisms were
distracting from the main aim which is ensure that a trace structure
is formed from Virtual Sets. I do think this method could have worked
if I had enough time, but the problem is that I didn't have the time
to spare.

In the aid of this simplicity, I decided to switch to the following
structure to represent injective Fin funcitons:

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

The way it works is that `nul` introduces an empty function from `Fin 0`
to some `Fin n`. Then each subsequent `inc` adds a single link
shifting the domain and codomain such that it is impossible to
construct a non-injective function.

I represent these functions as vectors of finite values, where the
position corresponds to each domain element, and the number is what
that element is mapped to. For example, let's introduce compact
notation to represent `Inj` functions.

We present the same function as an example in section
\ref{definition-of-injfun}, represented in figure \ref{fig:120}.

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
\caption{Plot of $(1\ 2\ 0)$. The bottom row is the domain and the top
row is the codomain. The arrow indicates the direction from domain to
codomain.}
\label{fig:120}
\end{figure}

In represented as an `Inj`, we build up from `nul 0` adding edges as
we go. We call `0` the 'slack' of the function, which is always equal
to the size of the codomain minus the domain. `inc`, `insert` and
`remove` operations all preserve the slack as we will see. `$` in the
below is the function application operator, used to make function
application right-associative, saving the use of parentheses.
```
f : Inj 3 3
f = inc f1 $ inc f1 $ inc f0 $ nul 0
-- f = inc f1 (inc f1 (inc f0 (nul 0)))
```

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
\node[below=2mm of box1.south] {\texttt{inc f0 \$ nul 0}};
\begin{scope}[xshift=4cm, local bounding box=box2]
  \dotrow{1}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{1}{a}{below}
  \end{scope}
  \draw[color=red,ultra thick] (a0) -- (b1);
  \draw (a1) -- (b0);
\end{scope}
\node[below=2mm of box2.south] {\texttt{inc f1 \$ inc f0 \$ nul 0}};
\begin{scope}[xshift=9cm, local bounding box=box3]
  \dotrow{2}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{2}{a}{below}
  \end{scope}
  \draw[color=red,ultra thick] (a0) -- (b1);
  \draw (a1) -- (b2);
  \draw (a2) -- (b0);
\end{scope}
\node[below=2mm of box3.south] {\texttt{inc f1 \$ inc f1 \$ inc f0 \$ nul 0}};
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
\caption{Construction of $(1\ 2\ 0)$ starting from \texttt{inc f0 \$ nul 0}.}
\label{fig:120-construction}
\end{figure}

This is read right to left. First we start with `nul 0` which is an
empty function with an empty codomain. The difference between the size
of the domain and the codomain is specified entirely by this `nul`
funciton.

0. Starting with `nul 0` means we having a slack of 0, which means we
   are construction a bijection, although this needs to be
   proven. In a sense, it is the measure of how close to a surjection the
   funciton is. Since the funciton is injective by construction, we know
   that the size of the range is equal to the range. So the value given
   to nul is the difference between the size of the codomain and the
   domain. This value remains constant as links are added.
1. Next we add a single link from f0 to f0. This is the only choice we
   have at this stage because we're creating a function from Fin 1 to Fin
   1 from `nul 0 : Fin 0 → Fin 0`.
2. The second link we add gives us two choices. We can either be
   parallel to the first link or cross over it. `(inc f0 $ inc f0 $ nul
   0)` is two parallel links. `(inc f1 $ inc f0 $ nul 0)` is two crossing
   links. Note that these are the only two bijections from Fin 2 to Fin 2
   available. We choose to cross in this example.
3. Finally the third link can either cross over both (`f2`), cross
   over just one (`f1`), or not cross at all (`f0`). We choose the middle
   option and end up with a cycle. Note that after nul 0, we three
   choices, $1 × 2 × 3 = 3!$. Every inc that is added increases the type
   of the Fin added by 1. Therefore, starting with `nul 0` to make `Inj m
   m`, there are m! options, which indicates that we're representing all
   possibilities. (Though it still needs to be checked that there is only
   one way to construct each function.)

The general formula for the number of injective finite functions
between any two sets of size $m$ and $n$ is:

$$
  \frac{n!}{(n-m)!}
$$

This has the nice properties that all constructions are necessarily
injective, since it is impossible to construct two outputs that are
the same, for example (0 0) : Fin 2 cannot be constructed. This is
because each insertion 'splices' the output domain, which means
shifting all links to all codomain elements that are greater than or
equal to the new link's codomain element. We'll introduce splice
operations in the next section.
