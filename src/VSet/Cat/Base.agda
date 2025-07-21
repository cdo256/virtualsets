module VSet.Cat.Base where

open import Cubical.Categories.Category
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Compose

-- _⊙_ : ∀ {X Y Z} → [ Y ↣ Z ] → [ X ↣ Y ] → [ X ↣ Z ]

VSetCat : Category _ _
VSetCat = record
  { ob = SomeFin
  ; Hom[_,_] = [_↣_]
  ; id = id↣
  ; _⋆_ = λ f g → g ⊙ f
  ; ⋆IdL = {!!}
  ; ⋆IdR = {!!}
  ; ⋆Assoc = {!!}
  ; isSetHom = {!!}
  }
