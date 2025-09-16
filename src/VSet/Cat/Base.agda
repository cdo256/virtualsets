module VSet.Cat.Base where

open import VSet.Prelude
open import Cubical.Categories.Category
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Compose.Properties
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.InjFun.Equality
open import VSet.Data.InjFun.Injection
open import VSet.Data.InjFun.Properties 

VSetCat : Category _ _
VSetCat = record
  { ob = ℕ
  ; Hom[_,_] = Inj
  ; id = λ {n} → idInj n
  ; _⋆_ = _∘⁻ʲ_
  ; ⋆IdL = ∘ʲ-idR
  ; ⋆IdR = ∘ʲ-idL
  ; ⋆Assoc = λ x y z → ∘ʲ-assoc z y x
  ; isSetHom = isSetInj
  }

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

-- Conjecture that these categories are equivalent.
