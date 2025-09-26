<!--
```
module Dissertation.TransformInjTensor where

open import Cubical.Data.List.Base hiding (elim; [_])
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Prod.Base
open import Cubical.Data.Sum.Base hiding (elim)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base
open import VSet.Data.Inj.Order
open import VSet.Data.Inj.Properties
open import VSet.Prelude hiding (id)
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Elementary.Base
open import VSet.Transform.Inj.Inverse.Base
open import VSet.Transform.Inj.Tensor.Properties hiding (Id⊕Id≡Id) 
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Constructions.BinProduct
open import VSet.Cat.Inj using (InjCat)

private
  variable
    l m n l' m' n' l'' m'' n'' : ℕ
```
-->

## Defining Tensor on \texttt{\large Inj} {#defining-tensor-on-inj}

We now define a tensor product on `Inj`. We don't get as far as
proving all of the coherence results, however due to time constraints,
I wasn't able to finish the proof of the coherence results..

We start by defining a 'shift' operator, which is a bit like fshift,
but applies to all result. The idea is that shift increases all of the
output values, effectively shifting the window to the left.

```
shift1 : ∀ {m n} → (f : Inj m n) → Inj m (suc n)
shift1 (nul _) = nul _
shift1 (inc b f) = inc (fsuc b) (shift1 f)
```

```
shift : ∀ {m n} → (l : ℕ) → (f : Inj m n) → Inj m (l + n)
shift zero f = f
shift (suc l) f = shift1 (shift l f)
```

Next we define the tensor, as injecting in the left case, and shifting
in the right case. and a unit.
```
infixl 30 _⊕_ -- \o+
tensor : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
tensor (nul m') g = shift m' g
tensor {n' = n'} (inc b f) g = inc (finject n' b) (tensor f g)
_⊕_ :  ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
f ⊕ g = tensor f g

𝟘 : Inj 0 0
𝟘 = nul 0
```

## Associator on `⊕`


```
open import Cubical.Data.Prod.Base
open import Cubical.Data.Sum.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.List.Base hiding (elim; [_])
open import Cubical.Data.Maybe.Base hiding (elim)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inj.Inverse.Base

shift1-tensor : (f : Inj m m') (g : Inj n n')
             → (shift1 f) ⊕ g ≡ shift1 (f ⊕ g)
shift1-tensor {m} {m'} {n} {n'} (nul m') g = refl
shift1-tensor {m} {m'} {n} {n'} (inc b f) g =
  shift1 (inc b f) ⊕ g ≡⟨ refl ⟩
  inc (fsuc b) (shift1 f) ⊕ g
    ≡⟨ refl ⟩
  inc (finject n' (fsuc b)) (shift1 f ⊕ g)
    ≡⟨ cong₂ inc (finject-fsuc-reorder b) (shift1-tensor f g) ⟩
  inc (fsuc (finject n' b)) (shift1 (f ⊕ g))
    ≡⟨ refl ⟩
  shift1 (inc (finject n' b) (f ⊕ g))
    ≡⟨ refl ⟩
  shift1 (inc b f ⊕ g) ▯

shift-tensor-cast
  : (l' : ℕ) (f : Inj m m') (g : Inj n n')
  → (shift l' f) ⊕ g ≡ jcast refl (+-assoc l' m' n') (shift l' (f ⊕ g))
shift-tensor-cast {m} {m'} {n} {n'} zero f g = 
  shift zero f ⊕ g ≡⟨ refl ⟩
  shift zero (f ⊕ g) ≡⟨ sym (jcast-loop _ _ _) ⟩
  jcast refl (+-assoc zero m' n') (shift zero (f ⊕ g)) ▯
shift-tensor-cast {m} {m'} {n} {n'} (suc l') f g =
  (shift (suc l') f) ⊕ g
    ≡⟨ refl ⟩
  (shift1 (shift l' f)) ⊕ g
    ≡⟨ shift1-tensor (shift l' f) g ⟩
  shift1 ((shift l' f) ⊕ g)
    ≡⟨ cong shift1 (shift-tensor-cast l' f g) ⟩
  shift1 (jcast refl (+-assoc l' m' n') (shift l' (f ⊕ g)))
    ≡⟨ {!!} ⟩
  jcast refl (cong suc (+-assoc l' m' n')) (shift1 (shift l' (f ⊕ g)))
    ≡⟨ refl ⟩
  jcast refl (+-assoc (suc l') m' n') (shift (suc l') (f ⊕ g)) ▯

-- jcast-reorder
--   : ∀ {m m' n n' : ℕ}
--   → (ϕ : ℕ → ℕ) (ψ : ℕ → ℕ) (η : {x y : ℕ} → Inj x y → Inj (ϕ x) (ψ y))
--   → (p : m ≡ m') (q : n ≡ n') (f : Inj m n)
--   → jcast (cong ϕ p) (cong ψ q) (η f)
--   ≡ η (jcast p q f)
-- jcast-reorder {zero} {zero} {n} {n'} ϕ ψ η p q (nul _) = {!!}
-- jcast-reorder {zero} {suc m'} {n} {n'} ϕ ψ η p q (nul _) = {!!}
-- jcast-reorder {suc m} {m'} {n} {n'} ϕ ψ η p q (inc b f) = {!!}

shift-tensor : (l' : ℕ) (f : Inj m m') (g : Inj n n')
             → (shift l' f) ⊕ g ≡ subst2 Inj refl (+-assoc l' m' n') (shift l' (f ⊕ g))
shift-tensor {m} {m'} {n} {n'} zero f g =
  shift zero f ⊕ g ≡⟨ sym (transportRefl (shift zero f ⊕ g)) ⟩
  transport refl (shift zero (f ⊕ g)) ≡⟨ refl ⟩
  subst2 Inj refl (+-assoc zero m' n') (shift zero (f ⊕ g)) ▯
shift-tensor {m} {m'} {n} {n'} (suc l') f g =
  (shift (suc l') f) ⊕ g
    ≡⟨ refl ⟩
  (shift1 (shift l' f)) ⊕ g
    ≡⟨ shift1-tensor (shift l' f) g ⟩
  shift1 ((shift l' f) ⊕ g)
    ≡⟨ cong shift1 (shift-tensor l' f g) ⟩
  shift1 (subst2 Inj refl (+-assoc l' m' n') (shift l' (f ⊕ g)))
    ≡⟨ sym (subst2-reorder Inj (λ x → x) suc shift1 refl
                           (+-assoc l' m' n') (shift l' (f ⊕ g))) ⟩
  subst2 Inj refl (+-assoc (suc l') m' n') (shift (suc l') (f ⊕ g)) ▯
```

module _ {l l' m m' n n' : ℕ} where
  α-p-dom : l + (m + n) ≡ (l + m) + n
  α-p-dom = +-assoc l m n

  α-p-cod : l' + (m' + n') ≡ (l' + m') + n'
  α-p-cod = +-assoc l' m' n'

  α-p : Inj (l + (m + n)) (l' + (m' + n'))
      ≡ Inj ((l + m) + n) ((l' + m') + n')
  α-p =
    cong₂ Inj (+-assoc l m n) (+-assoc l' m' n')

  α-iso : Iso (Inj (l + (m + n)) (l' + (m' + n')))
              (Inj ((l + m) + n) ((l' + m') + n'))
  α-iso = pathToIso α-p

  α : Inj (l + (m + n)) (l' + (m' + n')) → Inj ((l + m) + n) ((l' + m') + n')
  α = Iso.fun α-iso 

  α⁻¹ : Inj ((l + m) + n) ((l' + m') + n') → Inj (l + (m + n)) (l' + (m' + n')) 
  α⁻¹ = Iso.inv α-iso 

assoc : {l l' m m' n n' : ℕ} → (f : Inj l l') (g : Inj m m') (h : Inj n n')
  → ((f ⊕ g) ⊕ h) ≡ transport (α-p {l} {l'}) (f ⊕ (g ⊕ h))
assoc {zero} {l'} {m} {m'} {n} {n'} (nul _) g h =
  (nul l' ⊕ g) ⊕ h
    ≡⟨ refl ⟩
  (shift l' g) ⊕ h
    ≡⟨ shift-tensor l' g h ⟩
  subst2 Inj refl (+-assoc l' m' n') (shift l' (g ⊕ h))
    ≡⟨ refl ⟩
  subst2 Inj (+-assoc zero m n) (+-assoc l' m' n') (nul l' ⊕ (g ⊕ h)) ▯
assoc {suc l} {suc l'} {m} {m'} {n} {n'} (inc b f) g h =
  (inc b f ⊕ g) ⊕ h
    ≡⟨ refl ⟩
  (inc (finject m' b) (f ⊕ g)) ⊕ h
    ≡⟨ refl ⟩
  inc (finject n' (finject m' b)) ((f ⊕ g) ⊕ h)
    ≡⟨ cong (λ ○ → inc ○ ((f ⊕ g) ⊕ h)) (finject-+ (suc l') m' n' b)  ⟩
  inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b)) ((f ⊕ g) ⊕ h)
    ≡⟨ cong (inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b)))
            (assoc f g h) ⟩
  inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b))
      (subst2 Inj (+-assoc l m n) (+-assoc l' m' n') (f ⊕ (g ⊕ h)))
    ≡⟨ sym (subst2-inc-reorder (+-assoc l m n) (+-assoc l' m' n')
                               (finject (m' + n') b) (f ⊕ (g ⊕ h))) ⟩
  subst2 Injsuc (+-assoc l m n) (+-assoc l' m' n')
        (inc (finject (m' + n') b) (f ⊕ (g ⊕ h)))
    ≡⟨ refl ⟩
  subst2 Inj (+-assoc (suc l) m n) (+-assoc (suc l') m' n')
        (inc b f ⊕ (g ⊕ h)) ▯

unassoc : (f : Inj l l') (g : Inj m m') (h : Inj n n')
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


## Tensor Category Construction (unfinished)

<!--
```
Id⊕Id≡Id : Id {m} ⊕ Id {n} ≡ Id {m + n}
Id⊕Id≡Id {zero} {n} = refl
Id⊕Id≡Id {suc m} {n} = cong (inc f0) (Id⊕Id≡Id {m} {n})
```
-->

```
open Category
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

