module VSet.Cat.Monoidal where

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
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties
open import VSet.Cat.Base

open Category

VSetProdCat : Category _ _
VSetProdCat = VSetCat ×C VSetCat

⊕-ob : VSetProdCat .ob → VSetCat .ob
⊕-ob (m , n) = m + n

⊕-hom : {x y : VSetProdCat .ob} → VSetProdCat [ x , y ] → VSetCat [ ⊕-ob x , ⊕-ob y ]
⊕-hom (f , g) = f ⊕ g

⊕-id : {x : VSetProdCat  .ob}
     → ⊕-hom {x = x} {y = x} (VSetProdCat .id)
     ≡ VSetCat .id {x = ⊕-ob x}
⊕-id {(m , n)} =
  ⊕-hom {x = (m , n)} {y = (m , n)} (VSetProdCat .id)
    ≡⟨ refl ⟩
  ⊕-hom {x = (m , n)} {y = (m , n)} (𝟙 , 𝟙)
    ≡⟨ refl ⟩
  𝟙 {m} ⊕ 𝟙 {n}
    ≡⟨ 𝟙⊕𝟙≡𝟙 {m} {n} ⟩
  𝟙 {m + n} ▯

⊕-seq : {x y z : VSetProdCat .ob} (f : VSetProdCat [ x , y ]) (g : VSetProdCat [ y , z ])
      → ⊕-hom (f ⋆⟨ VSetProdCat ⟩ g) ≡ (⊕-hom f) ⋆⟨ VSetCat ⟩ (⊕-hom g)
⊕-seq {(l , l')} {(m , m')} {(n , n')} (f , f') (g , g') =
  ⊕-hom ((f , f') ⋆⟨ VSetProdCat ⟩ (g , g'))
    ≡⟨ {!!} ⟩
  ⊕-hom (f ∘⁻ʲ g , f' ∘⁻ʲ g') 
    ≡⟨ {!!} ⟩
  (f ⊕ f') ∘⁻ʲ (g ⊕ g') ▯

tensorStr : TensorStr VSetCat
tensorStr = record
  { ─⊗─ = record
    { F-ob = ⊕-ob
    ; F-hom = ⊕-hom
    ; F-id = ⊕-id
    ; F-seq = ⊕-seq
    }
  ; unit = {!!}
  }
