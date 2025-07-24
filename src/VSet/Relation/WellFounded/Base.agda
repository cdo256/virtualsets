module VSet.Relation.WellFounded.Base where

open import VSet.Prelude
open import Cubical.Relation.Binary.Base 
open import VSet.Function.Base
open import VSet.Relation.Definitions
open import Cubical.Induction.WellFounded

open BinaryRelation
open Acc

private
  variable
    a b c d e ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Type a
    B : Type b
    C : Type c
    D : Type d

mapRel : ∀ (f : A → B) → (_≺_ : Rel B B ℓ₁) → Rel A A _
mapRel f _≺_ x y = f x ≺ f y 

module _ (f : A → B) (_≺_ : Rel B B ℓ₁) where
  _≺'_ : Rel A A _
  _≺'_ = mapRel f _≺_

  accB→accA : (x : A) → Acc _≺_ (f x) → Acc _≺'_ x
  accB→accA x (acc r) = acc (λ y y≺'x → accB→accA y (r (f y) y≺'x))

  mapRel-wellFounded : WellFounded _≺_ → WellFounded _≺'_
  mapRel-wellFounded wf x = accB→accA x (wf (f x))
