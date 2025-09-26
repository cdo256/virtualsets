```
module Dissertation.InjMonoidal where

open import VSet.Prelude hiding (id)
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base 
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inj.Elementary.Base
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Compose.Properties
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties hiding (Id⊕Id≡Id; apply-⊕-fshift; apply-⊕-finject; fsplice-finject; fsplice-finject-finject)

open Category
```

<!--
```
InjCat : Category _ _
InjCat = record
  { ob = ℕ
  ; Hom[_,_] = Inj
  ; id = λ {n} → idInj n
  ; _⋆_ = _∘⁻ʲ_
  ; ⋆IdL = ∘ʲ-idR
  ; ⋆IdR = ∘ʲ-idL
  ; ⋆Assoc = λ x y z → ∘ʲ-assoc z y x
  ; isSetHom = isSetInj
  }
```
-->

# Construction of a Monoidal Category in `Inj`

Now we have a tensor operator, `⊕`, we want to show that this tensor
is a well-behaved bifunctor, meaning that it maps identities to
identites and that the two ways of composing tensors commute:
`(f ⊕ g) ∘ (f' ⊕ g') ≡ (f ∘ f') ⊕ (g ∘ g')`.
Recall that bifunctor is just a functor from a product category.


```
InjProdCat : Category _ _
InjProdCat = InjCat ×C InjCat
```

We define the object part to simply be the sum of the two naturals:
```
⊕-ob : InjProdCat .ob → InjCat .ob
⊕-ob (m , n) = m + n
```

The morphism part is the tensor product we have defined.
```
⊕-hom : {x y : InjProdCat .ob} → InjProdCat [ x , y ]
      → InjCat [ ⊕-ob x , ⊕-ob y ]
⊕-hom (f , g) = f ⊕ g
```

We show that the tensor of two identity functions are identity
recursively, which shows that identitities tensor to get another
identity morphism.
```
Id⊕Id≡Id : {m n : ℕ} → Id {m} ⊕ Id {n} ≡ Id {m + n}
Id⊕Id≡Id {zero} {n} = refl
Id⊕Id≡Id {suc m} {n} = cong (inc f0) (Id⊕Id≡Id {m} {n})

⊕-id : {x : InjProdCat  .ob}
     → ⊕-hom {x = x} {y = x} (InjProdCat .id)
     ≡ InjCat .id {x = ⊕-ob x}
⊕-id {(m , n)} = Id⊕Id≡Id {m} {n}
```

The final step for constructing a bifunctor is left incomplete. It
requires filling in a hole given in the below functions. This is
another issue I'm sure I could work out given enough time, but I had
to stop somewhere, so I've left the holes in the below funcitons.

`apply-⊕-fshift` handle the case of applying a tensor to the `fshift`
case, and `apply-⊕-finject` handles the case of `finject`. Ther idea
is similar between them, recursing on the structure of the left-most
function, `f`, with `apply-⊕-fshift` also recursing on whether the
first mapped element goes to `f0`, or another value. I am highlighting
just the unfinished cases, with the full code being availble at
VSet.Transform.Inj.Tensor.Properties in the provided source.
```
apply-⊕-fshift
  : {k l m n : ℕ} (f : Inj k l) (g : Inj m n) (a : Fin m)
  → apply (f ⊕ g) (fshift k a) ≡ fshift l (apply g a)
apply-⊕-fshift {suc k} {suc l} {suc m} {suc n} (inc (fsuc b) f) g a =
  apply (inc (fsuc b) f ⊕ g) (fshift (suc k) a)
    ≡⟨ refl ⟩
  apply (inc (finject (suc n) (fsuc b)) (f ⊕ g)) (fshift (suc k) a)
    ≡⟨ refl ⟩
  apply (inc (fsuc (finject (suc n) b)) (f ⊕ g)) (fsuc (fshift k a))
    ≡⟨ refl ⟩
  fsplice (fsuc (finject (suc n) b)) (apply (f ⊕ g) (fshift k a))
    ≡⟨ cong (fsplice (fsuc (finject (suc n) b))) (apply-⊕-fshift f g a) ⟩
  fsplice (fsuc (finject (suc n) b)) (fshift l (apply g a))
    ≡⟨ {!!} ⟩
  fsuc (fshift l (apply g a))
    ≡⟨ refl ⟩
  fshift (suc l) (apply g a) ▯
```

<!--
```
apply-⊕-fshift {zero} {l} {m} {n} (nul l) g a =
  apply (nul l ⊕ g) a 
    ≡⟨ refl ⟩
  apply (shift l g) a 
    ≡⟨ apply-shift l g a ⟩
  fshift l (apply g a) ▯
apply-⊕-fshift {suc k} {suc l} {suc m} {n} (inc fzero f) g a =
  apply (inc fzero f ⊕ g) (fshift (suc k) a)
    ≡⟨ refl ⟩
  apply (inc fzero f ⊕ g) (fsuc (fshift k a))
    ≡⟨ refl ⟩
  apply (inc (finject n fzero) (f ⊕ g)) (fsuc (fshift k a))
    ≡⟨ refl ⟩
  fsplice (finject n fzero) (apply (f ⊕ g) (fshift k a))
    ≡⟨ cong (fsplice (finject n fzero)) (apply-⊕-fshift f g a) ⟩
  fsplice (finject n fzero) (fshift l (apply g a))
    ≡⟨ refl ⟩
  fsplice fzero (fshift l (apply g a))
    ≡⟨ refl ⟩
  fsuc (fshift l (apply g a))
    ≡⟨ refl ⟩
  fshift (suc l) (apply g a) ▯
```
-->

```
fsplice-finject
  : {k l m n : ℕ} (a : Fin k) (b : Fin (suc k))
  → fsplice (finject n b) (finject n a)
  ≡ finject n (fsplice b a)
fsplice-finject {k} {l} {m} {n} fzero fzero = refl
fsplice-finject {k} {l} {m} {n} fzero (fsuc b) = refl
fsplice-finject {k} {l} {m} {n} (fsuc a) fzero = refl
fsplice-finject {k} {l} {m} {n} (fsuc a) (fsuc b) =
  cong fsuc (fsplice-finject a b)

apply-⊕-finject
  : {k l m n : ℕ} (f : Inj k l) (g : Inj m n) (a : Fin k)
  → apply (f ⊕ g) (finject m a) ≡ finject n (apply f a) 
apply-⊕-finject {suc k} {suc l} {m} {n} (inc b f) g fzero =
  apply (inc b f ⊕ g) (finject m fzero)
    ≡⟨ refl ⟩
  apply (inc (finject n b) (f ⊕ g)) fzero
    ≡⟨ refl ⟩
  finject n b
    ≡⟨ refl ⟩
  finject n (apply (inc b f) fzero) ▯
apply-⊕-finject {suc k} {suc l} {m} {n} (inc b f) g (fsuc a) =
  apply (inc b f ⊕ g) (finject m (fsuc a))
    ≡⟨ refl ⟩
  apply (inc (finject n b) (f ⊕ g)) (fsuc (finject m a))
    ≡⟨ refl ⟩
  fsplice (finject n b) (apply (f ⊕ g) (finject m a))
    ≡⟨ cong (fsplice (finject n b)) (apply-⊕-finject f g a) ⟩
  fsplice (finject n b) (finject n (apply f a))
    ≡⟨ fsplice-finject (apply f a) b ⟩
  finject n (fsplice b (apply f a))
    ≡⟨ refl ⟩
  finject n (apply (inc b f) (fsuc a)) ▯

fsplice-finject-finject : {l m n : ℕ} → (a : Fin (suc l)) (b : Fin l)
            → fsplice (finject n a) (finject n b)
            ≡ finject n (fsplice a b)
fsplice-finject-finject fzero fzero = refl
fsplice-finject-finject fzero (fsuc b) = refl
fsplice-finject-finject (fsuc a) fzero = refl
fsplice-finject-finject (fsuc a) (fsuc b) =
  cong fsuc (fsplice-finject-finject a b)
```

We then define the extensional version of ⊕-seq
```
⊕-seq-ext
  : {l l' m m' n n' : ℕ}
  → (f : Inj l m) (f' : Inj l' m')
  → (g : Inj m n) (g' : Inj m' n')
  → (x : Fin (l + l'))
  → apply ((g ∘ʲ f) ⊕ (g' ∘ʲ f')) x
  ≡ apply ((g ⊕ g') ∘ʲ (f ⊕ f')) x
```

<!--
```
⊕-seq-ext {zero} {l'} {m} {m'} {n} {n'} (nul m) f' g g' x =
  apply ((g ∘ʲ (nul m)) ⊕ (g' ∘ʲ f')) x
    ≡⟨ refl ⟩
  apply ((nul n) ⊕ (g' ∘ʲ f')) x
    ≡⟨ refl ⟩
  apply (shift n (g' ∘ʲ f')) x
    ≡⟨ apply-shift n (g' ∘ʲ f') x ⟩
  fshift n (apply (g' ∘ʲ f') x)
    ≡⟨ cong (fshift n) (sym (apply-apply g' f' x)) ⟩
  fshift n (apply g' (apply f' x))
    ≡⟨ sym (apply-⊕-fshift g g' (apply f' x)) ⟩
  apply (g ⊕ g') (fshift m (apply f' x))
    ≡⟨ cong (apply (g ⊕ g')) (sym (apply-shift m f' x)) ⟩
  apply (g ⊕ g') (apply (shift m f') x)
    ≡⟨ refl ⟩
  apply (g ⊕ g') (apply ((nul m) ⊕ f') x)
    ≡⟨ apply-apply (g ⊕ g') ((nul m) ⊕ f') x ⟩
  apply ((g ⊕ g') ∘ʲ ((nul m) ⊕ f')) x ▯
⊕-seq-ext {suc l} {l'} {suc m} {m'} {suc n} {n'} (inc fzero f) f' (inc c g) g' fzero =
  apply ((inc c g ∘ʲ inc fzero f) ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  apply (inc (apply (inc c g) fzero) g ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  finject n' (apply (inc c g) fzero)
    ≡⟨ refl ⟩
  finject n' c
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) fzero 
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) (apply (inc (finject m' fzero) (f ⊕ f')) fzero)
    ≡⟨ refl ⟩
  apply (inc c g ⊕ g') (apply (inc fzero f ⊕ f') fzero)
    ≡⟨ apply-apply (inc c g ⊕ g') (inc fzero f ⊕ f') fzero ⟩
  apply ((inc c g ⊕ g') ∘ʲ (inc fzero f ⊕ f')) fzero ▯
⊕-seq-ext {suc l} {l'} {suc m} {m'} {suc n} {n'} (inc (fsuc b) f) f' (inc c g) g' fzero =
  apply ((inc c g ∘ʲ inc (fsuc b) f) ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  apply (inc (apply (inc c g) (fsuc b)) g ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  finject n' (apply (inc c g) (fsuc b))
    ≡⟨ refl ⟩
  finject n' (fsplice c (apply g b))
    ≡⟨ sym (fsplice-finject-finject c (apply g b)) ⟩
  fsplice (finject n' c) (finject n' (apply g b))
    ≡⟨ cong (fsplice (finject n' c)) (sym (apply-⊕-finject g g' b)) ⟩
  fsplice (finject n' c) (apply (g ⊕ g') (finject m' b))
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) (fsuc (finject m' b))
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) (apply (inc (finject m' (fsuc b)) (f ⊕ f')) fzero)
    ≡⟨ refl ⟩
  apply (inc c g ⊕ g') (apply (inc (fsuc b) f ⊕ f') fzero)
    ≡⟨ apply-apply (inc c g ⊕ g') (inc (fsuc b) f ⊕ f') fzero ⟩
  apply ((inc c g ⊕ g') ∘ʲ (inc (fsuc b) f ⊕ f')) fzero ▯
⊕-seq-ext {suc l} {l'} {suc m} {m'} {suc n} {n'} (inc b f) f' (inc c g) g' (fsuc x) =
  apply ((inc c g ∘ʲ inc b f) ⊕ (g' ∘ʲ f')) (fsuc x)
    ≡⟨ refl ⟩
  apply ((inc (apply (inc c g) b) (remove b (inc c g) ∘ʲ f)) ⊕ (g' ∘ʲ f')) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc (finject n' (apply (inc c g) b)) ((remove b (inc c g) ∘ʲ f) ⊕ (g' ∘ʲ f'))) (fsuc x)
    ≡⟨ refl ⟩
  fsplice (finject n' (apply (inc c g) b)) (apply ((remove b (inc c g) ∘ʲ f) ⊕ (g' ∘ʲ f')) x)
    ≡⟨ {!!} ⟩
  apply (inc (finject n' c) (g ⊕ g')) (apply (inc (finject m' b) (f ⊕ f')) (fsuc x))
    ≡⟨ refl ⟩
  apply (inc c g ⊕ g') (apply (inc b f ⊕ f') (fsuc x))
    ≡⟨ apply-apply (inc c g ⊕ g') (inc b f ⊕ f') (fsuc x) ⟩
  apply ((inc c g ⊕ g') ∘ʲ (inc b f ⊕ f')) (fsuc x) ▯
```
-->

And use that to prove `⊕-seq`. Note again that since earlier
definitions aren't full proven yet, there are still some gaps left to
verify before this is a full functor construction.
```
⊕-seq : {x y z : InjProdCat .ob} (f : InjProdCat [ x , y ]) (g : InjProdCat [ y , z ])
      → ⊕-hom (f ⋆⟨ InjProdCat ⟩ g) ≡ (⊕-hom f) ⋆⟨ InjCat ⟩ (⊕-hom g)
⊕-seq {(l , l')} {(m , m')} {(n , n')} (f , f') (g , g') =
  injExt ((g ∘ʲ f) ⊕ (g' ∘ʲ f'))
         ((g ⊕ g') ∘ʲ (f ⊕ f'))
         (⊕-seq-ext f f' g g')
```

```
tensorStr : TensorStr InjCat
tensorStr = record
  { ─⊗─ = record
    { F-ob = ⊕-ob
    ; F-hom = ⊕-hom
    ; F-id = ⊕-id
    ; F-seq = ⊕-seq
    }
  ; unit = 0
  }
```
