module VirtualSet where

-- open import Data.Empty
-- open import Data.List
--   using (List; []; _∷_; filter; map)
-- import Data.List.Membership.Setoid
-- open import Data.List.NonEmpty
--   using (List⁺) renaming (_∷_ to _∷⁺_)
-- open import Data.List.Relation.Unary.All as All
--   using (All; all?)
-- open import Data.List.Relation.Unary.Any as Any
--   using (Any; map; here; there)
open import Data.Product
  using (Σ-syntax; _×_; proj₁; proj₂)
open import Data.Product.Base as Product
  using (∃; _×_; _,_)
-- open import Data.Sum
--   using (inj₁; inj₂)
open import Level
  using (_⊔_; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.Bundles
  using (DecSetoid)
-- open import Relation.Binary.Definitions
--   using (Decidable)
-- open import Relation.Nullary.Decidable.Core
--   using (yes; no; _×-dec_ )
-- open import Relation.Nullary.Negation
--   using (¬_)

open import FiniteSet

private
  variable
    c ℓ : Level.Level

module _ {Dom : DecSetoid c ℓ} where
  open DecSetoid Dom renaming (Carrier to D) 
  open import Data.List.Membership.DecSetoid Dom
  
  module _ {A X Y : FiniteSet} {_ : disjoint A X} {_ : disjoint A Y}
           (f : X ∪ A →′ Y ∪ A) (A : FiniteSet) where
    _-′_ : (X →′ Y)
    _-′_ = record
      { ⟦_⟧ = g
      ; isRelHomomorphism = {!!}
      }
      where
        g : toSet X → toSet Y
        g (x , px) = {!!}


    f′ : toSet X → toSet Y
    f′ (a , pa) with ⟦ f ⟧ (a , pa)
    ... | z = {!!}
