<!--
```
module Dissertation.TransformInjElementary where

open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base
open import VSet.Data.Inj.Order
open import VSet.Prelude

private
  variable
    l m n l' m' n' : ℕ
```
-->

## Elementary Operations on \texttt{\large Inj} {#elementary-operations-on-inj}

We define four elementary operations on our inductive injective
function representation (`Inj`) that allow us to add, remove, and
rearrange edges. These capture how the structure of injections can be
manipulated while preserving injectivity.

### Insert

The `insert` operation adds a new edge between a domain element and a
codomain element, shifting the existing connections to preserve
injectivity.

```
insert : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
       → (f : Inj m n) → Inj (suc m) (suc n)
insert fzero b f = inc b f
insert (fsuc a) b (inc c f) =
  inc (fsplice b c) (insert a (fcross c b) f)
```

Diagrammatically (Figure \ref{fig:insert}), inserting means creating a
new edge, splicing it into the domain and codomain.

```latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  \begin{scope}[local bounding box=boxA]
    \dotrow{2}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{1}{a}{below}
    \end{scope}
    \draw (a0) -- (b2);
    \draw (a1) -- (b1);
  \end{scope}
  \node[below=2mm of boxA.south] {\texttt{inc f2 \$ inc f1 \$ nul 1}};

  \begin{scope}[xshift=5cm, local bounding box=boxB]
    \dotrow{3}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{2}{a}{below}
    \end{scope}
    \draw (a0) -- (b3);
    \draw[color=red,ultra thick] (a1) -- (b2);
    \draw (a2) -- (b1);
  \end{scope}
  \node[below=2mm of boxB.south] {\texttt{inc f1 \$ inc f2 \$ inc f1 \$ nul 1}};

  \draw[
    ultra thick,
    -{>[length=8mm, width=8mm]},
    shorten >=0.7cm,
    shorten <=0.7cm
    ] (boxA.east) -- (boxB.west) node[below=5mm, midway] {insert 1 2};
\end{tikzpicture}
\caption{Example step of insert: adds a domain and codomain element, inserting the new edge.}
\label{fig:insert}
\end{figure}
```

### Remove

The `remove` operation deletes one edge from the injection, shifting
everything back down.

```
remove : ∀ {m n} → (a : Fin (suc m))
       → (f : Inj (suc m) (suc n)) → Inj m n
remove fzero (inc b f) = f
remove {suc m} {suc n} (fsuc a) (inc c f) =
  inc (fcross (apply f a) c) (remove a f)
```

This is illustrated in Figure \ref{fig:remove}: one edge is deleted
and the codomain is compressed.

```latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  \begin{scope}[local bounding box=boxB]
    \dotrow{3}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{2}{a}{below}
    \end{scope}
    \draw (a0) -- (b3);
    \draw[color=red,ultra thick] (a1) -- (b2);
    \draw (a2) -- (b1);
  \end{scope}
  \node[below=2mm of boxB.south] {\texttt{inc f1 \$ inc f2 \$ inc f1 \$ nul 1}};
  \begin{scope}[local bounding box=boxA, xshift=6cm]
    \dotrow{2}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{1}{a}{below}
    \end{scope}
    \draw (a0) -- (b2);
    \draw (a1) -- (b1);
  \end{scope}
  \node[below=2mm of boxA.south] {\texttt{inc f2 \$ inc f1 \$ nul 1}};
  \draw[
    ultra thick,
    -{>[length=8mm, width=8mm]},
    shorten >=0.7cm,
    shorten <=0.7cm
    ] (boxB.east) -- (boxA.west) node[below=5mm, midway] {remove 1 2};
\end{tikzpicture}
\caption{Remove deletes a domain/codomain edge, shifting as needed.}
\label{fig:remove}
\end{figure}
```


### Bubble

The `bubble` operation allows us to "shift" all outputs around a pivot point in the codomain.

```
bubble : ∀ {m n} → (b : Fin (suc n))
       → (f : Inj m n) → Inj m (suc n)
bubble b (nul _) = nul _
bubble b (inc c f) =
  inc (fsplice b c) (bubble (fcross c b) f)
```

This operation is shown in Figure \ref{fig:bubble}, where all the
edges are redirected around the pivot `b`. Bubble is equivalent to
composing `f` with an injective function

```latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  
  \begin{scope}[local bounding box=boxA]
    \dotrow{2}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{1}{a}{below}
    \end{scope}
    \draw (a0) -- (b2);
    \draw (a1) -- (b1);
  \end{scope}
  \node[below=2mm of boxA.south] {\texttt{inc f2 \$ inc f1 \$ nul 1}};
  \begin{scope}[xshift=6cm, local bounding box=boxB]
    \dotrow{3}{b}{above}
    \node[pivot, fit=(b2)] {};
    \begin{scope}[yshift=-2cm]
      \dotrow{1}{a}{below}
    \end{scope}
    \draw (a0) -- (b3);
    \draw (a1) -- (b1);
  \end{scope}
  \node[below=2mm of boxB.south] {\texttt{inc f3 \$ inc f1 \$ nul 2}};
  \draw[
    ultra thick,
    -{>[length=8mm, width=8mm]},
    shorten >=0.7cm,
    shorten <=0.7cm
    ] (boxA.east) -- (boxB.west) node[below=5mm, midway] {bubble 2};
\end{tikzpicture}
\caption{Bubble creates a new unoccupied codomain slot at the highlighted position.}
  \label{fig:bubble}
\end{figure}
```

### Excise

Finally, `excise` removes a domain element without shifting the
codomain. It is implemented in terms of `remove` and `bubble`.

```
excise : ∀ {m n} → (a : Fin (suc m))
       → (f : Inj (suc m) (suc n)) → Inj m (suc n)
excise a f = bubble (apply f a) (remove a f)
```

As shown in Figure \ref{fig:excise}, excision removes a mapping while
preserving the overall codomain mapping by bubbling around the target
of the deleted edge. This is equivalent to first removing the edge
then splicing at the target.

```latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  
  \begin{scope}[local bounding box=boxC]
    \dotrow{3}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{2}{a}{below}
    \end{scope}
    \draw (a0) -- (b3);
    \draw[color=red,ultra thick] (a1) -- (b2);
    \draw (a2) -- (b1);
  \end{scope}
  \node[below=2mm of boxC.south] {\texttt{inc f1 \$ inc f2 \$ inc f1 \$ nul 1}};
  
  \begin{scope}[xshift=6cm, local bounding box=boxD]
    \dotrow{3}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{1}{a}{below}
    \end{scope}
    \draw (a0) -- (b3);
    \draw (a1) -- (b1);
  \end{scope}
  \node[below=2mm of boxD.south] {\texttt{inc f3 \$ inc f1 \$ nul 2}};
  \draw[
    ultra thick,
    -{>[length=8mm, width=8mm]},
    shorten >=0.7cm,
    shorten <=0.7cm
    ] (boxC.east) -- (boxD.west) node[below=5mm, midway] {excise 1};
\end{tikzpicture}
\caption{Excise removes highlighted domain/codomain edge, then bubbles its image to preserve codomain size.}
\label{fig:excise}
\end{figure}
```
