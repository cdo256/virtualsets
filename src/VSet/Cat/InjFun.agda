module VSet.Cat.InjFun where

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Monoidal
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.InjFun.Equality
open import VSet.Data.InjFun.Injection
open import VSet.Data.InjFun.Properties 
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Prelude hiding (id)
open import VSet.Transform.InjFun.Tensor 
open import VSet.Transform.InjFun.Compose

open Category

InjFunCat : Category _ _
InjFunCat = record
  { ob = ℕ
  ; Hom[_,_] = [_↣_]
  ; id = id↣
  ; _⋆_ = (λ f g → g ↣∘↣ f)
  ; ⋆IdL = ↣∘↣-idR
  ; ⋆IdR = ↣∘↣-idL
  ; ⋆Assoc = λ f g h → ↣∘↣-assoc h g f
  ; isSetHom = isSetInjFun
  }

InjFunProdCat : Category _ _
InjFunProdCat = InjFunCat ×C InjFunCat

⊕-ob : InjFunProdCat .ob → InjFunCat .ob
⊕-ob (m , n) = m + n

⊕-hom : {x y : InjFunProdCat .ob} → InjFunProdCat [ x , y ]
      → InjFunCat [ ⊕-ob x , ⊕-ob y ]
⊕-hom (f , g) = f ⊕ g

⊕-id : {x : InjFunProdCat  .ob}
     → ⊕-hom {x = x} {y = x} (InjFunProdCat .id)
     ≡ InjFunCat .id {x = ⊕-ob x}
⊕-id {(m , n)} =
  ⊕-hom {x = (m , n)} {y = (m , n)} (InjFunProdCat .id)
    ≡⟨ refl ⟩
  ⊕-hom {x = (m , n)} {y = (m , n)} (Id , Id)
    ≡⟨ refl ⟩
  Id {m} ⊕ Id {n}
    ≡⟨ Id⊕Id≡Id {m} {n} ⟩
  Id {m + n} ▯

⊕-seq : {x y z : InjFunProdCat .ob} (f : InjFunProdCat [ x , y ]) (g : InjFunProdCat [ y , z ])
      → ⊕-hom (f ⋆⟨ InjFunProdCat ⟩ g) ≡ (⊕-hom f) ⋆⟨ InjFunCat ⟩ (⊕-hom g)
⊕-seq {(l , l')} {(m , m')} {(n , n')} (f , f') (g , g') =
  ⊕-hom ((f , f') ⋆⟨ InjFunProdCat ⟩ (g , g'))
    ≡⟨ {!!} ⟩
  ⊕-hom (f ∘⁻ʲ g , f' ∘⁻ʲ g') 
    ≡⟨ {!!} ⟩
  (f ⊕ f') ∘⁻ʲ (g ⊕ g') ▯

tensorStr : TensorStr InjFunCat
tensorStr = record
  { ─⊗─ = record
    { F-ob = ⊕-ob
    ; F-hom = ⊕-hom
    ; F-id = ⊕-id
    ; F-seq = ⊕-seq
    }
  ; unit = {!!}
  }
