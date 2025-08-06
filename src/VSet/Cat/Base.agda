module VSet.Cat.Base where

open import Cubical.Categories.Category
open import Cubical.Data.Nat
open import VSet.Data.Inj.Base 
open import VSet.Transform.Compose.Base
open import VSet.Transform.Compose.Properties

VSetCat : Category _ _
VSetCat = record
  { ob = ℕ
  ; Hom[_,_] = Inj
  ; id = λ {n} → idInj n
  ; _⋆_ = _∘⁻ʲ_
  ; ⋆IdL = ∘ʲ-idR
  ; ⋆IdR = ∘ʲ-idL
  ; ⋆Assoc = {!!}
  ; isSetHom = {!!}
  }
