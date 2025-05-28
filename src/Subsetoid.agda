module Subsetoid where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; Σ-syntax; ∃; uncurry; swap; Σ)
open import Data.Sum.Base using (_⊎_; [_,_])
open import Function.Base using (_∘_; _|>_)
open import Level using (Level; _⊔_; 0ℓ; suc; Lift)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary as Nullary using (¬_; Dec; True)

-- open import Data.List using (List; []; _∷_; map; _++_)
-- open import Data.List.Relation.Unary.Enumerates.Setoid
--   using (IsEnumeration)
-- open import Data.Product
--   using (Σ-syntax; _,_; proj₁; proj₂)
-- open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
-- open import Data.Sum.Relation.Binary.Pointwise using ()
-- open import Level using (_⊔_; 0ℓ; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.Bundles using (Setoid)
-- open import Relation.Binary.Core using (Rel)
-- open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
-- open import Relation.Binary.PropositionalEquality
--   using (_≡_) renaming (isEquivalence to ≡isEquiv)
open import Function.Definitions using (Congruent)

-- open FiniteSetoid T using (S; enum)
-- open Setoid S using (_≈_)
--  renaming (Carrier to A; isEquivalence to equiv)
-- open import Relation.Binary
open import Relation.Binary.Definitions
  using (_Respects_; Reflexive; Symmetric; Transitive)
-- open import Relation.Binary.Structures
--   using (IsEquivalence)
-- open IsEquivalence equiv
-- open import Relation.Unary using (Pred)
open import Function.Definitions using (Congruent)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    S : Setoid a ℓ
    -- B : Setoid b ℓ
    -- C : Setoid c ℓ

module _ (S : Setoid a ℓ) where
  open Setoid S renaming (Carrier to A)

  record Pred : Set (suc (a ⊔ ℓ)) where
    field
      P : (A → Set ℓ)
      resp : (P Respects _≈_)
open import Relation.Binary.Structures using (IsEquivalence)

module _ {S : Setoid a ℓ} where
  open Setoid S
    using (_≈_; isEquivalence)
    renaming (Carrier to A)
  open IsEquivalence isEquivalence public

  ∅ : Pred S
  ∅ = record
    { P = λ _ → Lift ℓ ⊥
    ; resp = λ _ x → x
    }

  ｛_｝ : A → Pred S
  ｛ a ｝ = record
    { P = λ y → a ≈ y 
    ; resp = λ xy ax → trans ax xy
    }

  U : Pred S
  U = record
    { P = λ _ → Lift ℓ ⊤
    ; resp = λ _ x → x
    }

  infix 4 _∈_ _∉_
  
  _∈_ : A → Pred S → Set _
  x ∈ P' = Pred.P P' x
  
  _∉_ : A → Pred S → Set _
  x ∉ P' = ¬ x ∈ P'

  infix 4 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_ _≐_
  
  _⊆_ : Pred S → Pred S → Set _
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  _⊇_ : Pred S → Pred S → Set _
  P ⊇ Q = Q ⊆ P

  _⊈_ : Pred S → Pred S → Set _
  P ⊈ Q = ¬ (P ⊆ Q)

  _⊉_ : Pred S → Pred S → Set _
  P ⊉ Q = ¬ (P ⊇ Q)

  _⊂_ : Pred S → Pred S → Set _
  P ⊂ Q = P ⊆ Q × Q ⊈ P

  _⊃_ : Pred S → Pred S → Set _
  P ⊃ Q = Q ⊂ P

  _⊄_ : Pred S → Pred S → Set _
  P ⊄ Q = ¬ (P ⊂ Q)

  _⊅_ : Pred S → Pred S → Set _
  P ⊅ Q = ¬ (P ⊃ Q)

  _≐_ : Pred S → Pred S → Set _
  P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

  module _  (P : Pred S) where
    open Pred P renaming (P to P')

    restrict : Setoid _ _
    restrict = record
        { Carrier = Σ A P'
        ; _≈_ = λ (x , _) (y , _) → x ≈ y 
        ; isEquivalence = record
          { refl = refl
          ; sym = sym
          ; trans = trans
          }
        }
