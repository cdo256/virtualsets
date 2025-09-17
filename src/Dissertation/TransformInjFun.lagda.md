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
open import VSet.Data.Sum.Properties
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
```
-->

\begin{verbatim}[hide]
module DissertationTex.TransformInjFun where

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
open import VSet.Data.Sum.Properties
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
\end{verbatim}

# Tensor Product on `InjFun`

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
identity arrow.
```
Id⊕Id≡Id : {m n : ℕ} → Id {m} ⊕ Id {n} ≈ Id {m + n}
Id⊕Id≡Id {m} {n} = record { p = refl ; q = refl ; path = r }
  where
    r : (⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n) ≡ id
    r =
      ⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m n ∘ ○ ∘ +→⊎ m n) ⊎-map-id≡id ⟩
      ⊎→+ m n ∘ +→⊎ m n
        ≡⟨ funExt (⊎+sect m n) ⟩
      id ▯
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
  α-p-fun = {!cong₂ (λ A B → A → B) α-p-dom α-p-cod!}

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

```
funPath→InjFunPath : {m m' : ℕ} → (f g : [ m ↣ m' ])
                   → fst f ≡ fst g → f ≡ g
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

```
mapsplit-l
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → ⊎-map (⊎→+ l' m' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ l m) (fst h)
  ≡   ⊎-map (⊎→+ l' m') id
    ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
    ∘ ⊎-map (+→⊎ l m) id
mapsplit-l {l} {l'} {m} {m'} {n} {n'} f g h =
  ⊎-map (⊎→+ l' m' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ l m) (id ∘ fst h ∘ id)
    ≡⟨ sym (⊎-map-∘ _ _ _ _) ⟩
    ⊎-map (⊎→+ l' m') id
  ∘ ⊎-map (⊎-map (fst f) (fst g) ∘ +→⊎ l m) (fst h)
    ≡⟨ sym (cong (⊎-map (⊎→+ l' m') id ∘_) (⊎-map-∘ _ _ _ _)) ⟩
    ⊎-map (⊎→+ l' m') id
  ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
  ∘ ⊎-map (+→⊎ l m) id ▯
```

```
mapsplit-r
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → ⊎-map (fst f) (⊎→+ m' n' ∘ ⊎-map (fst g) (fst h) ∘ +→⊎ m n)
  ≡   ⊎-map id (⊎→+ m' n')
    ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
    ∘ ⊎-map id (+→⊎ m n)
mapsplit-r {l} {l'} {m} {m'} {n} {n'} f g h =
  ⊎-map (id ∘ fst f ∘ id) (⊎→+ m' n' ∘ ⊎-map (fst g) (fst h) ∘ +→⊎ m n)
    ≡⟨ sym (⊎-map-∘ _ _ _ _) ⟩
    ⊎-map id (⊎→+ m' n')
  ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h) ∘ +→⊎ m n)
    ≡⟨ sym (cong (⊎-map id (⊎→+ m' n') ∘_) (⊎-map-∘ _ _ _ _)) ⟩
    ⊎-map id (⊎→+ m' n')
  ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
  ∘ ⊎-map id (+→⊎ m n) ▯
```

```
expand-l
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → fst ((f ⊕ g) ⊕ h) ≡
      ⊎→+ (l' +ℕ m') n'
    ∘ ⊎-map (⊎→+ l' m') id
    ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
    ∘ ⊎-map (+→⊎ l m) id
    ∘ +→⊎ (l +ℕ m) n
expand-l {l} {l'} {m} {m'} {n} {n'} f g h =
  fst ((f ⊕ g) ⊕ h)
    ≡⟨ refl ⟩
  ⊎→+ (l' +ℕ m') n' ∘ ⊎-map (fst (f ⊕ g)) (fst h) ∘ +→⊎ (l +ℕ m) n
    ≡⟨ refl ⟩
    ⊎→+ (l' +ℕ m') n'
  ∘ ⊎-map (⊎→+ l' m' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ l m) (fst h)
  ∘ +→⊎ (l +ℕ m) n
    ≡⟨ (cong (λ ○ → _ ∘ ○ ∘ _) (mapsplit-l f g h)) ⟩
    ⊎→+ (l' +ℕ m') n'
  ∘ ⊎-map (⊎→+ l' m') id
  ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
  ∘ ⊎-map (+→⊎ l m) id
  ∘ +→⊎ (l +ℕ m) n ▯
```

```
expand-r
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → fst (f ⊕ (g ⊕ h)) ≡
      ⊎→+ l' (m' +ℕ n')
    ∘ ⊎-map id (⊎→+ m' n')
    ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
    ∘ ⊎-map id (+→⊎ m n)
    ∘ +→⊎ l (m +ℕ n)
expand-r {l} {l'} {m} {m'} {n} {n'} f g h =
  fst (f ⊕ (g ⊕ h))
    ≡⟨ refl ⟩
  ⊎→+ l' (m' +ℕ n') ∘ ⊎-map (fst f) (fst (g ⊕ h)) ∘ +→⊎ l (m +ℕ n)
    ≡⟨ refl ⟩
  ⊎→+ l' (m' +ℕ n')
  ∘ ⊎-map (fst f)
           (⊎→+ m' n' ∘ ⊎-map (fst g) (fst h) ∘ +→⊎ m n)
  ∘ +→⊎ l (m +ℕ n)
    ≡⟨ (cong (λ ○ → _ ∘ ○ ∘ _) (mapsplit-r f g h)) ⟩
  ⊎→+ l' (m' +ℕ n')
  ∘ ⊎-map id (⊎→+ m' n')
  ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
  ∘ ⊎-map id (+→⊎ m n)
  ∘ +→⊎ l (m +ℕ n) ▯
```

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
assoc-ext' {zero} {l'} {zero} {m'} {suc n} {n'} f g h fzero =
  ⊎→+ (l' +ℕ m') n'
   (⊎-map (⊎→+ l' m') id
    (⊎-map (⊎-map f g) h
     (⊎-map (+→⊎ 0 0) id
      (+→⊎ 0 (suc n)
       (f0)))))
    ≡⟨ {!!} ⟩
  (subst Fin α-p-cod
   (⊎→+ l' (m' +ℕ n')
    (⊎-map id (⊎→+ m' n')
     (⊎-map f (⊎-map g h)
      (⊎-map id (+→⊎ 0 (suc n))
       (+→⊎ 0 (0 +ℕ (suc n))
        (subst Fin (sym α-p-dom)
         (f0)))))))) ▯
assoc-ext' {zero} {l'} {zero} {m'} {suc n} {n'} f g h (fsuc x) = {!!}
assoc-ext' {zero} {l'} {suc m} {m'} {n} {n'} f g h x = {!!}
assoc-ext' {suc l} {l'} {m} {m'} {n} {n'} f g h x = {!!}
```

```
assoc-ext : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → ∀ x → fst ((f ⊕ g) ⊕ h) x ≡ fst (α {l} {l'} (f ⊕ (g ⊕ h))) x
assoc-ext {zero} {l'} {zero} {m'} {suc n} {n'} f g h fzero =
  fst ((f ⊕ g) ⊕ h) f0
    ≡⟨ refl ⟩
  fst (α (f ⊕ (g ⊕ h))) f0 ▯
assoc-ext {zero} {l'} {zero} {m'} {suc n} {n'} f g h (fsuc x) = {!!}
assoc-ext {zero} {l'} {suc m} {m'} {n} {n'} f g h x = {!!}
assoc-ext {suc l} {l'} {m} {m'} {n} {n'} f g h x = {!!}
```

```
assoc : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → ((f ⊕ g) ⊕ h) ≡ α {l} {l'} (f ⊕ (g ⊕ h))
assoc {l} {l'} {m} {m'} {n} {n'} f g h =
  funPath→InjFunPath ((f ⊕ g) ⊕ h) (α (f ⊕ (g ⊕ h))) {!fun-assoc!}
```

```
unassoc : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → (f ⊕ (g ⊕ h)) ≡ (α⁻¹ {l} {l'}) ((f ⊕ g) ⊕ h)
unassoc {l} {l'} {m} {m'} {n} {n'} f g h =
  let α-p = α-p {l} {l'} {m} {m'} {n} {n'}
  in
  (f ⊕ (g ⊕ h))
    ≡⟨ sym (transport⁻Transport α-p (f ⊕ (g ⊕ h))) ⟩
  transport (sym α-p )
    (transport α-p (f ⊕ (g ⊕ h)))
    ≡⟨ sym (cong (transport (sym α-p)) (assoc f g h)) ⟩
  transport (sym α-p) ((f ⊕ g) ⊕ h) ▯
```

```
-- α₁ : ∀ {m m' m'' n n' n''}
--    → (f : [ m ↣ n ]) (g : [ m' ↣ n' ]) (h : [ m'' ↣ n'' ])
--    → f ⊕ (g ⊕ h) → {!(f ⊕ g) ⊕ h!}
```

```
-- ⊕-triangle : ∀ {m m' n n'} → (f : [ m ↣ n ]) (g : [ m' ↣ n' ])
--            → {!!}
```
