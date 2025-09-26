<!--
```
module Dissertation.TransformInjFun where

open import Cubical.Core.Primitives
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary.Base
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.Fin.SumSplit
  using (⊎≅+; ⊎→+; +→⊎) renaming (sect to ⊎+sect; retr to ⊎+retr)
open import VSet.Data.InjFun.Equality
open import VSet.Data.InjFun.Injection
open import VSet.Data.InjFun.Properties
open import VSet.Data.Nat
open import VSet.Data.Nat hiding (_+_; ¬-<-zero)
open import VSet.Data.Nat hiding (¬-<-zero)
open import VSet.Data.Nat using (ℕ; zero; suc; _+_)
open import VSet.Data.Nat.WellFounded
open import VSet.Data.Sum.Properties hiding (⊎-assoc)
open import VSet.Data.SumTree.Base hiding (α; α⁻¹)
open import VSet.Data.SumTree.Metrics
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Path
open import VSet.Prelude
open import VSet.Relation.WellFounded.Base
open import VSet.Relation.WellFounded.Lex
open import VSet.Data.Fin.Minus using (_∖_; _—_; del; ins)
open import VSet.Transform.InjFun.Tensor using (expand-l; expand-r)
```
-->


## Tensor Product on \texttt{\large InjFun} {#tensor-product-on-injfun}

We now move to detail operations and properties on `InjFun`.

First we define compositional identity (`Id`) and monoidal unit (`𝟘`).

```
Id : ∀ {X} → [ X ↣ X ]
Id = (λ x → x) , λ x y eq' → eq'

𝟘 : [ 0 ↣ 0 ]
𝟘 = ↣-id ⟦ 0 ⟧
```

We use additive notation (`𝟘` and `⊕`) for the tensor product and
identity because our tensor operation merges two injections via the
coproduct map `↣-map-⊎`, summing both domain and codomain sizes. The
tensor is defined as a composition of three steps (which appear from
right to left in the definition):
- `≅to↣ (flip-≅ (⊎≅+ k m))` splits the input into `Fin k` or `Fin m`.
- `↣-map-⊎ f g` applies `f` or `g`, depending on the split.
- `≅to↣ (⊎≅+ l n)` combines the outputs.

The Agda code is:
```
tensor : ∀ {k l m n : ℕ} → [ k ↣ l ] → [ m ↣ n ] → [ k + m ↣ l + n ]
tensor {k} {l} {m} {n} f g = ≅to↣ (⊎≅+ l n) ↣∘↣ ↣-map-⊎ f g ↣∘↣ ≅to↣ (flip-≅ (⊎≅+ k m))

infixl 30 _⊕_
_⊕_ : ∀ {k l m n : ℕ} → [ k ↣ l ] → [ m ↣ n ] → [ k + m ↣ l + n ]
f ⊕ g = tensor f g
```

`⊕` forms a coproduct structure on the category of injective functions.

We then prove some properties about this tensor. `Id⊕Id≡Id` states
that placing two identity arrows 'side by side' results in another
identity arrow. We define the function part first, and then use the fact that `is-injective` is a proposition to show the equality holds for the dependent sum. 
```
id⊕id≡id : {m n : ℕ} → ⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n ≡ id
id⊕id≡id {m} {n} =
  ⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n
    ≡⟨ cong (λ ○ → ⊎→+ m n ∘ ○ ∘ +→⊎ m n) ⊎-map-id≡id ⟩
  ⊎→+ m n ∘ +→⊎ m n
    ≡⟨ funExt (⊎+sect m n) ⟩
  id ▯


Id⊕Id≡Id : {m n : ℕ} → Id {m} ⊕ Id {n} ≡ Id {m + n}
Id⊕Id≡Id {m} {n} = cong₂ _,_ id⊕id≡id s
  where r : subst is-injective id⊕id≡id (snd (Id {m} ⊕ Id {n})) ≡ snd (Id {m + n})
        r = isProp-is-injective id (subst is-injective id⊕id≡id (snd (Id {m} ⊕ Id {n}))) (snd (Id {m + n}))
        s : (λ i → is-injective (id⊕id≡id i))
          [ snd (Id {m} ⊕ Id {n}) ≡ snd (Id {m + n}) ]
        s = compPathP' (subst-filler is-injective id⊕id≡id (snd (Id {m} ⊕ Id {n}))) r
```

For convenience we have a short-hand for adding an identity arrow on
the left or right.
```
ladd : ∀ {l m : ℕ} → (A : ℕ) → [ l ↣ m ] → [ A + l ↣ A + m ]
ladd {l} {m} A f = (Id {A}) ⊕ f

radd : ∀ {l m : ℕ} → (A : ℕ) → [ l ↣ m ] → [ l + A ↣ m + A ]
radd {l} {m} A f = f ⊕ (Id {A})
```

\begin{figure}[h]
  \centering
  \begin{tikzcd}
    m + n \arrow[r, "f \oplus g", tail]
    \arrow[rr, "{(f' \circ f) \oplus (g' \circ g')}"', bend right] &
    m'+n' \arrow[r, "f' \oplus g'", tail] & m''+n''
  \end{tikzcd}
  \caption{Direct sum of injections preserves composition: the composition of direct sums matches the direct sum of compositions, i.e., this diagram commutes.}
  \label{fig:sum-preserves-composition}
\end{figure}

Next we show that for the operation `_⊕_`: The property
`⊕-preserves-∘` demonstrates that the direct sum (coproduct) of
injective functions is compatible with composition: composing two
pairs of injections separately and then taking their direct sum yields
the same result as first taking the direct sums and then composing
those. Formally, for injections `f`, `f'`, `g`, `g'`, the equation
`(f' ∘ f) ⊕ (g' ∘ g) = (f' ⊕ g') ∘ (f ⊕ g)` ensures the tensor operation
respects function composition, and that the sum operation acts
functorially on the category of injective functions. See figure \ref{fig:sum-preserves-composition}.

```
⊕-preserves-∘
  : ∀ {m m' m'' n n' n''}
  → (f : [ m ↣ m' ]) (f' : [ m' ↣ m'' ]) (g : [ n ↣ n' ]) (g' : [ n' ↣ n'' ])
  → ((f' ↣∘↣ f) ⊕ (g' ↣∘↣ g)) ≈ ((f' ⊕ g') ↣∘↣ (f ⊕ g))
```

<!--
```
⊕-preserves-∘ {m} {m'} {m''} {n} {n'} {n''} f f' g g' =
  record { p = refl ; q = refl ; path = e }
  where
    e : ⊎→+ m'' n'' ∘ ⊎-map (fst f' ∘ fst f) (fst g' ∘ fst g) ∘ +→⊎ m n
      ≡   (⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ +→⊎ m' n')
        ∘ (⊎→+ m'  n'  ∘ ⊎-map (fst f)  (fst g)  ∘ +→⊎ m  n)
    e =
      ⊎→+ m'' n'' ∘ ⊎-map (fst f' ∘ fst f) (fst g' ∘ fst g) ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m'' n'' ∘ ○ ∘ +→⊎ m n)
                (sym (⊎-map-∘ (fst f) (fst f') (fst g) (fst g'))) ⟩
      ⊎→+ m'' n'' ∘ (⊎-map (fst f') (fst g') ∘ ⊎-map (fst f) (fst g)) ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m'' n'' ∘ (⊎-map (fst f') (fst g') ∘ ○ ∘ ⊎-map (fst f) (fst g)) ∘ +→⊎ m n)
                (sym (funExt (⊎+retr m' n'))) ⟩
      ⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ (+→⊎ m' n' ∘
        ⊎→+ m' n') ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n
        ≡⟨ refl ⟩
      (⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ +→⊎ m' n') ∘
        ⊎→+ m' n' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n ▯
```
-->

Now we begin defining the associator `α` for tensor products:

- `α-p-dom` and `α-p-cod` is the domain and codomain indexes respectively.
- `α-p` is the path between the type of the right associated function
  and the left associated depdendent sum.
- `α-p-fun` is the same as `α-p` but for just the function part.
- `α-iso` is the map as an isomorphism, which is for proving
  associator is a natural isomorphism.
- Finally, `α` is the right-to-left transport, and `α⁻¹` is the left-to-right
  transport.
```
module _ {l l' m m' n n' : ℕ} where
  α-p-dom : l + (m + n) ≡ (l + m) + n
  α-p-dom = +-assoc l m n

  α-p-cod : l' + (m' + n') ≡ (l' + m') + n'
  α-p-cod = +-assoc l' m' n'

  α-p : [ (l + (m + n)) ↣ (l' + (m' + n')) ]
      ≡ [ ((l + m) + n) ↣ ((l' + m') + n') ]
  α-p = cong₂ [_↣_] (+-assoc l m n) (+-assoc l' m' n')

  α-p-fun : (Fin (l + (m + n)) → Fin (l' + (m' + n')))
          ≡ (Fin ((l + m) + n) → Fin ((l' + m') + n'))
  α-p-fun = cong₂ FinFun α-p-dom  α-p-cod

  α-iso : Iso [ (l + (m + n)) ↣ (l' + (m' + n')) ]
              [ ((l + m) + n) ↣ ((l' + m') + n') ]
  α-iso = pathToIso α-p

  α : [ (l + (m + n)) ↣ (l' + (m' + n')) ]
    → [ ((l + m) + n) ↣ ((l' + m') + n') ]
  α = Iso.fun α-iso

  α⁻¹ : [ ((l + m) + n) ↣ ((l' + m') + n') ]
      → [ (l + (m + n)) ↣ (l' + (m' + n')) ]
  α⁻¹ = Iso.inv α-iso
```

We make use of a handy result: For a pair of `InjFun`'s to be
equal, it is sufficient that their function parts are equal.

```
funPath→InjFunPath : {m m' : ℕ} → (f g : [ m ↣ m' ])
                   → fst f ≡ fst g → f ≡ g
```

<!--
```
funPath→InjFunPath {m} {m'} (f , f-inj) (g , g-inj) f≡g =
  f , f-inj
    ≡⟨ cong₂ _,_ f≡g (subst-filler is-injective f≡g f-inj) ⟩
  g , f-inj'
    ≡⟨ cong (g ,_)
            (isProp-is-injective
              g f-inj' g-inj) ⟩
  g , g-inj ▯
  where
    f-inj' : is-injective g
    f-inj' = subst is-injective f≡g f-inj
```
-->


We will need ⊎-assoc which gives an isomorphism between the two ways of
associating sums three values with a sum. We abbreviate the
definition, which is spelled out fully in VSet.Data.Sum CITE.

```
⊎-assoc : {A B C : Type} → A ⊎ (B ⊎ C) ≅ (A ⊎ B) ⊎ C
⊎-assoc = record
  { fun = f
  ; inv = g
  ; leftInv = retr
  ; rightInv = sect
  }
  where
    f : {A B C : Type} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
    g : {A B C : Type} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C) 
    sect : section f g
    retr : retract f g
```

<!--
```
    f (inl a) = inl (inl a)
    f (inr (inl b)) = inl (inr b)
    f (inr (inr c)) = inr c
    g (inl (inl a)) = inl a
    g (inl (inr b)) = inr (inl b)
    g (inr c) = inr (inr c)
    sect (inl (inl a)) = refl
    sect (inl (inr b)) = refl
    sect (inr c) = refl
    retr (inl a) = refl
    retr (inr (inl b)) = refl
    retr (inr (inr c)) = refl
```
-->

Proving tensor associativity in the general case requires proving this.
```
assoc-ext' : {l l' m m' n n' : ℕ}
  → (f : Fin l → Fin l') (g : Fin m → Fin m') (h : Fin n → Fin n')
  → ∀ x
  → (⊎→+ (l' +ℕ m') n'
     (⊎-map (⊎→+ l' m') id
      (⊎-map (⊎-map f g) h 
       (⊎-map (+→⊎ l m) id
        (+→⊎ (l +ℕ m) n
         (x))))))
  ≡ (subst Fin α-p-cod
     (⊎→+ l' (m' +ℕ n')
      (⊎-map id (⊎→+ m' n')
       (⊎-map f (⊎-map g h)
        (⊎-map id (+→⊎ m n)
         (+→⊎ l (m +ℕ n)
          (subst Fin (sym α-p-dom)
           (x))))))))
```

I expect that proving this should be relatively straight-forward by
splitting it into parts, however this was a lemma that I haven't had
time to return to.

<!--
```
assoc-ext' f g h x = _
```
-->

## Trace operations on \texttt{\large InjFun} {#trace-operations-on-injfun}

The final construction for the dependent sum '`InjFun`' approach is
the `trace` operator. In principle, a trace is an operator that
decreases the domain and codomain of an injective function by the same
amount. It will be easiest to start thinking about a trace of $1$,
that we call `pred` (for predecessor), and then define the trace
operator as the repeated `pred` operations.

Start by considering an injective function, the graph of which is
given by figure \ref{fig:trace-steps} as step 0. The information flows in one
direction, indicated by the arrow on the right. This example is
bijective but we don't require surjection. Now the predecessor
operation ('pred' or 'trace 1') on this function is visualized as a
backward 'feedback' edge from 0 in the codomain back to 0 in the
domain. We consider each node to have at most one input and one
output, meaning that 'd0' (short for domain element 0) can't be
accessed from an input function, since it already has one output and
one input. Likewise 'c0' (codomain element 0) already has one input
and output, so there are no extra 'connection points' to take the
output from. Hence the domain has been restricted to $\{1, 2\}$ and
the range to $\{1, 2, 3\}$, as given in \ref{fig:trace-steps} step
2. By convention, we shift all the values down by a fixed amount so
that we always have a domain and codomain composed of a consecutive
sequence starting from 0. The final result is given by figure
\ref{fig:trace-steps} as step 3.

```latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm, every node/.style={inner sep=0pt}]

\matrix[matrix of nodes, column sep=4cm, row sep=5cm] (m) {
\node[inner sep=0pt] (boxTL) {
  \begin{tikzpicture}[thickedge, node distance=7mm]
    \dotrow{3}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{2}{a}{below}
    \end{scope}
    \draw[midarrow] (a0) -- (b2);
    \draw[midarrow] (a1) -- (b0);
    \draw[midarrow] (a2) -- (b3);
  \end{tikzpicture}
}; &
\node[inner sep=0pt] (boxTR) {
  \begin{tikzpicture}[thickedge, node distance=7mm]
    \dotrow{3}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{2}{a}{below}
    \end{scope}
    \draw[midarrow] (a0) -- (b2);
    \draw[midarrow] (a1) -- (b0);
    \draw[midarrow] (a2) -- (b3);
    \draw[midarrow] (0,0)
      arc [start angle=0, end angle=180, radius=5mm]
      -- (-1,-2)
      arc [start angle=180, end angle=360, radius=5mm];
  \end{tikzpicture}
}; \\
\node[inner sep=0pt] (boxBL) {
  \begin{tikzpicture}[thickedge, node distance=7mm]
    \dotrow{2}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{1}{a}{below}
    \end{scope}
    \draw[midarrow] (a0) -- (b1);
    \draw[midarrow] (a1) -- (b2);
  \end{tikzpicture}
}; &
\node[inner sep=0pt] (boxBR) {
  \begin{tikzpicture}[thickedge, node distance=7mm]
    \dotrow{2}{b}{above}
    \begin{scope}[yshift=-2cm]
      \dotrow{1}{a}{below}
    \end{scope}
    \node[dotnode] (bn1) at (-1,0) {};
    \node[dotnode] (an1) at (-1,-2) {};
    \draw[midarrow] (an1) -- (b1);
    \draw[midarrow] (a0) -- (bn1);
    \draw[midarrow] (a1) -- (b2);
    \draw[midarrow] (-1,0)
      arc [start angle=0, end angle=180, radius=5mm]
      -- (-2,-2)
      arc [start angle=180, end angle=360, radius=5mm];
  \end{tikzpicture}
}; \\
};

\node[below=2mm of boxTL] {Step 0};
\node[below=2mm of boxTR] {Step 1};
\node[below=2mm of boxBR] {Step 2};
\node[below=2mm of boxBL] {Step 3};

\draw[ultra thick,-{>[length=8mm, width=8mm]}, shorten >=6mm, shorten <=6mm]
  (boxTL.east) -- (boxTR.west);
\draw[ultra thick,-{>[length=8mm, width=8mm]}, shorten >=6mm, shorten <=6mm]
  (boxTR.south) -- (boxBR.north);
\draw[ultra thick,-{>[length=8mm, width=8mm]}, shorten >=6mm, shorten <=6mm]
  (boxBR.west) -- (boxBL.east);

\end{tikzpicture}
\caption{Step by step procedure for $Tr₁ ((2\ 0\ 3))$. Start with the
graph of some injective function (step 0), add a cycle (step 1), shift
the indices (step 2), and finally join source directly up with
destination, (step 3) to get $(1 2)$.} \label{fig:trace-steps}
\end{figure}
```

We implement this by making use of subtypes of ℕ specifically we want
to formally define the notion of a finite set with an element taken out. We do this by defining a 'minus operator':

```
record _̣\̱_ (A : ℕ) (a : Fin A) : Type where
  constructor _–_
  field
    val : Fin A
    ne : a ≢ val
open _∖_
```

The idea is that we will use this definition to TODO

It is simply a pointed finite set, made up of a selected element
`a : Fin A`, such that each instance has a value `val : Fin A` paired with a proof of distinctness with `a`: `ne : a ≢ val`. We then prove some simple properties: 
```
s_—0 : {A : ℕ} (a : Fin A) → suc A ∖ fzero 
s a —0 = fsuc a — fzero≢fsuc {i = a}

0—s_ : {A : ℕ} (a : Fin A) → suc A ∖ fsuc a
0—s a = fzero — fsuc≢fzero {i = a}
```

`s a —0` removes 0 from Fin (suc A), leaving `fsuc a`, while `0—s a`
removes a successor element `fsuc a`, leaving 0. Next we construct
successor and predecessor functions on minus sets:
```
∖-suc : {A : ℕ} {a : Fin A} → A ∖ a → suc A ∖ fsuc a
∖-suc {suc A} (b — a≢b) = fsuc b — ≢cong fpred a≢b

∖-pred : {A : ℕ} {a : Fin A} → (b : suc A ∖ fsuc a) → (val b ≢ fzero) → A ∖ a
∖-pred {suc A} (fzero — a≢b) 0≢0 = absurd (0≢0 refl)
∖-pred {suc A} (fsuc b — a≢b) _ = b — ≢cong fsuc a≢b
```

Next we define insert and delete operations. Insert maps a finite set
to a finite set one larger, but with a hole. Delete on the other hand
goes in the opposite direction, mapping a finite set with a hole, to a
finite set one smaller. Both maps are bijections and respect order,
although that isn't proven here.
```
inṣ : {x : ℕ} → (a : ⟦ suc x ⟧) → ⟦ x ⟧ → (suc x ∖ a)
inṣ {suc x} fzero b = fsuc b — fzero≢fsuc
inṣ {suc x} (fsuc a) fzero = fzero — fsuc≢fzero
inṣ {suc x} (fsuc a) (fsuc b) =
  fsuc c — λ sa≡sc →
    let a≡c = fsuc-injective {suc x} {a} {c} sa≡sc
    in ne (inṣ a b) a≡c
  where
    c = val (inṣ a b)

deḷ : {x : ℕ} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
deḷ {ℕ.zero} fzero (fzero — 0≢0) = absurd (0≢0 refl)
deḷ {suc x} fzero (fzero — 0≢0) = absurd (0≢0 refl)
deḷ {suc x} fzero (fsuc b — a≢b) = b
deḷ {suc x} (fsuc a) (fzero — a≢b) = fzero
deḷ {suc x} (fsuc a) (fsuc b — a'≢b') =
  fsuc (deḷ {x} a (b — ≢cong fsuc a'≢b'))
```

## Definition of \texttt{\large pred} {#definition-of-pred}

\begin{figure}[ht]
\centering
\begin{tikzpicture}[thickedge, node distance=7mm]
  \begin{scope}[yshift=4cm]
    \dotrow{2}{e}{above}
  \end{scope}
  \begin{scope}[yshift=2cm]
    \dotrow{3}{d}{above}
  \end{scope}
  \begin{scope}[yshift=0cm]
    \dotrow{3}{c}{below}
  \end{scope}
  \begin{scope}[yshift=-2cm]
    \dotrow{2}{b}{below}
  \end{scope}
  \begin{scope}[yshift=-4cm]
    \dotrow{1}{a}{below}
  \end{scope}
  \node[pivot, fit=(b0)] {};
  \node[pivot, fit=(c2)] {};
  \node[pivot, fit=(d0)] {};
  \draw[midarrow] (d1) -- (e0);
  \draw[midarrow] (d2) -- (e1);
  \draw[midarrow] (d3) -- (e2);
  \draw[
    color=red,
    shorten >=1.5mm, shorten <=1.5mm,
    postaction={
      decorate,
      decoration={markings, mark=at position 0.7 with {\arrow{>}}} 
    }
  ] (c2) -- (d0);
  \draw[
    postaction={
      decorate,
      decoration={markings, mark=at position 0.6 with {\arrow{>}}} 
    }
  ] (c0) -- (d2);
  \draw[
    postaction={
      decorate,
      decoration={markings, mark=at position 0.4 with {\arrow{>}}} 
    }
  ] (c1) -- (d1);
  \draw[midarrow] (c3) -- (d3);
  \draw[color=red, midarrow, shorten >=1.5mm, shorten <=1.5mm] (b0) -- (c2);
  \draw[midarrow] (b1) -- (c0);
  \draw[midarrow] (b2) -- (c3);
  \draw[midarrow] (a0) -- (b1);
  \draw[midarrow] (a1) -- (b2);
\end{tikzpicture}
\caption{Chain of compositions to implement the trace of $(2\ 0\ 3)$.
From bottom to top: (a) `ins fzero` inserts a hole at location f0, (b)
The the function is applied and the hole is traced through from 0 to
2, (c) Next the hole and position 0 are swapped. }
\label{fig:trace-stack}
\end{figure}

We are now ready to define `Pred`. First fix a function `f'` with
domain `suc x` and range `suc y`. The pred operator cannot apply if
either the domain or range is empty, since it subtracts off an element
each time.

Our approach will be to chain maps, inserting a hole, mapping it with `f'`,
swapping that location with 0 and finally removing the bubble.

```
module Pred {x y : ℕ} (f' : [ suc x ↣ suc y ]) where
  open _∖_
```

First we split f' into its components:
```
  f = fst f'
  f-inj = snd f'
```

Now we construct the function-part of `pred`, this works as follows:
Given an input `i`, we shift it up to `fsuc i`, then, using the fact
that `f` is injective, we show that `f (fsuc i)` is not mapped to the
output of the trace path.
```
  g : ⟦ x ⟧ → ⟦ y ⟧
  g i =
    let f0≢fsi : f fzero ≢ f (fsuc i)
        f0≢fsi f0≡fsi = fzero≢fsuc (f-inj fzero (fsuc i) f0≡fsi) 
    in del (f fzero) (f (fsuc i) — f0≢fsi)
```

Next we prove injectivity, by chaining injectivity proofs. `di` is a proof that del is injectivity

```
  g-inj : is-injective g
  g-inj b₁ b₂ gb₁≡gb₂ = 
    let
      (c₁ — z≢c₁) = s b₁ —0
      (c₂ — z≢c₂) = s b₂ —0
    in
    fsuc-injective {i = b₁} {j = b₂}
       (f-inj c₁ c₂
         (del-inj
           (f fzero)
           (f c₁ — λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
           (f c₂ — λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
           gb₁≡gb₂))
```

Finally we construct the injective function `g'`, and use a module trick to
generate the operation `pred` from the previous construction of `g'`
from `g'`.
```
  g' : [ x ↣ y ]
  g' = g , g-inj

open Pred using () renaming (g' to pred) public
```

The operator `trace` comes from repeating `pred` `A` times.

```
trace : {X Y : ℕ} (A : ℕ) → (f : [ A + X ↣ A + Y ]) → [ X ↣ Y ]
trace zero f = f
trace (suc A) f = trace A (pred f)
```

This definition turned out to be cumbersome to work with as it
required explicitly transporting the proof of distinctness around.

I saw that lemmas were difficult to prove and saw that an alternative
approach using inductive types.
