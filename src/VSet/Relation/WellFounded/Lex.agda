------------------------------------------------------------------------
-- Originally from the Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a strict partial order.


module VSet.Relation.WellFounded.Lex where

open import VSet.Prelude
open import VSet.Function.Base
open import VSet.Relation.Definitions
open import Cubical.Relation.Binary.Base 
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

------------------------------------------------------------------------
-- A lexicographic ordering over products

×-Lex : (_<₁_ : Rel A A ℓ₂) (_≤₂_ : Rel B B ℓ₃) →
        Rel (A × B) (A × B) _
×-Lex _<₁_ _≤₂_ =
  (_<₁_ on proj₁) -⊎- ((_≡_ on proj₁) -×- (_≤₂_ on proj₂))

module _ {_<₁_ : Rel A A ℓ₂} {_<₂_ : Rel B B ℓ₃}
         {<₁-trans : isTrans _<₁_} {<₂-trans : isTrans _<₂_} where

  private
    _<ₗₑₓ_ = ×-Lex _<₁_ _<₂_

  -- FIXME: Convince agda of this fact
  {-# TERMINATING #-}
  ×-wellFounded : WellFounded _<₁_ →
                  WellFounded _<₂_ →
                  WellFounded _<ₗₑₓ_
  ×-wellFounded wf₁ wf₂ (x , y) = acc (×-acc (wf₁ x) (wf₂ y))
    where
    ×-acc : ∀ {x y} →
            Acc _<₁_ x → Acc _<₂_ y →
            WFRec _<ₗₑₓ_ (Acc _<ₗₑₓ_) (x , y)
    ×-acc {x} {y} (acc r1) (acc r2) (x' , y') (inl x'<x) =
        acc (×-acc (r1 x' x'<x) (wf₂ y'))
    ×-acc {x} {y} (acc r1) (acc r2) (x' , y') (inr (x'≡x , y'<y)) =
      acc r3
      where
        r3 : WFRec _<ₗₑₓ_ (Acc _<ₗₑₓ_) (x' , y')
        r3 (x'' , y'') (inl x''<x') =
          acc (×-acc (r1 x'' (subst (x'' <₁_) x'≡x x''<x'))
                (wf₂ y''))
        r3 (x'' , y'') (inr (x''≡x' , y''<y')) =
          subst (λ ○ → Acc _<ₗₑₓ_ (○ , y'')) (sym x''≡x')
                (acc (×-acc {x = x'} {y = y''}
                            (subst (Acc _<₁_) (sym x'≡x) (acc r1))
                            (r2 y'' (<₂-trans y'' y' y y''<y' y'<y))))
