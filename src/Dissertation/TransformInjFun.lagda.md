<!--
```
module Dissertation.TransformInjFun where

open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)
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
open import VSet.Data.Fin.Minus
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
open import VSet.Transform.InjFun.Tensor using (expand-l; expand-r)
```
-->


## Tensor Product on `InjFun`

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
