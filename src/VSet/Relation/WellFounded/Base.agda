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

mapRel-wellFounded
  : (f : A → B) → (_≺_ : Rel B B ℓ₁)
  → WellFounded _≺_ → WellFounded (mapRel f _≺_)
mapRel-wellFounded {A = A} {B = B} f _≺_ wf x = accB→accA x (wf (f x))
  where
    _≺'_ : Rel A A _
    _≺'_ = mapRel f _≺_
    accB→accA : (x : A) → Acc _≺_ (f x) → Acc _≺'_ x
    accB→accA x (acc r) = acc (λ y y≺'x → accB→accA y (r (f y) y≺'x))
