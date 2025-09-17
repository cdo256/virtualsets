module VSet.Cat.Inj where

open import VSet.Prelude hiding (id)
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Compose.Properties
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties

open Category

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


InjProdCat : Category _ _
InjProdCat = InjCat ×C InjCat

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
