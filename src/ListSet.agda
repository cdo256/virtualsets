
module ListSet where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_; Σ-syntax; ∃; uncurry; swap; Σ)
open import Data.Sum.Base using (_⊎_; [_,_]; inj₁; inj₂)
open import Function.Base using (_∘_; _|>_)
open import Level using (Level; _⊔_; 0ℓ; suc; Lift)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary as Nullary using (¬_; Dec; True)

open import Data.List using (List; []; _∷_; map; _++_)
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

-- open import Data.List.Relation.Unary.Enumerates.Setoid
--   using (IsEnumeration)
open import Data.List.Relation.Unary.Any using (here; there)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    S : Setoid a ℓ
    -- B : Setoid b ℓ
    -- C : Setoid c ℓ

module _ (S : Setoid a ℓ) where
  open Setoid S renaming (Carrier to A)
  open import Data.List.Membership.Setoid S
    using (_∈_)

  IsEnumeration : (xs : List A) → (P : A → Set ℓ) → Set _
  IsEnumeration xs P = ∀ ((x , px) : Σ A P) → x ∈' xs 

  record FinPred : Set (suc (a ⊔ ℓ)) where
    field
      P : A → Set ℓ
      resp : P Respects _≈_
      enum : List A
      isEnum : IsEnumeration enum P

open import Relation.Binary.Structures using (IsEquivalence)

module _ {S : Setoid a ℓ} where
  open Setoid S
    using (_≈_; isEquivalence)
    renaming (Carrier to A)
  open IsEquivalence isEquivalence public

  ∅ : FinPred S
  ∅ = record
    { P = λ _ → Lift ℓ ⊥
    ; resp = λ _ x → x
    ; enum = []
    ; isEnum = λ ()
    }

  ｛_｝ : A → FinPred S
  ｛ a ｝ = record
    { P = λ y → a ≈ y 
    ; resp = λ xy ax → trans ax xy
    ; enum = a ∷ []
    ; isEnum = λ (x , px) → here (sym px)
    }

  infix 4 _∈_ _∉_
  
  _∈_ : A → FinPred S → Set _
  x ∈ P' = FinPred.P P' x
  
  _∉_ : A → FinPred S → Set _
  x ∉ P' = ¬ x ∈ P'

  infix 4 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_ _≐_
  
  _⊆_ : FinPred S → FinPred S → Set _
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  _⊇_ : FinPred S → FinPred S → Set _
  P ⊇ Q = Q ⊆ P

  _⊈_ : FinPred S → FinPred S → Set _
  P ⊈ Q = ¬ (P ⊆ Q)

  _⊉_ : FinPred S → FinPred S → Set _
  P ⊉ Q = ¬ (P ⊇ Q)

  _⊂_ : FinPred S → FinPred S → Set _
  P ⊂ Q = P ⊆ Q × Q ⊈ P

  _⊃_ : FinPred S → FinPred S → Set _
  P ⊃ Q = Q ⊂ P

  _⊄_ : FinPred S → FinPred S → Set _
  P ⊄ Q = ¬ (P ⊂ Q)

  _⊅_ : FinPred S → FinPred S → Set _
  P ⊅ Q = ¬ (P ⊃ Q)

  _≐_ : FinPred S → FinPred S → Set _
  P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

  module _  (P₁ P₂ : FinPred S) where
    open import Data.List.Membership.Setoid S
      using () renaming (_∈_ to _∈'_)
    open import Data.List.Membership.Setoid.Properties
      using (∈-++⁺ˡ; ∈-++⁺ʳ) renaming ()

    open FinPred P₁ using ()
      renaming (P to Q₁; resp to resp₁; enum to enum₁; isEnum to isEnum₁)
    open FinPred P₂ using ()
      renaming (P to Q₂; resp to resp₂; enum to enum₂; isEnum to isEnum₂)

    P∪ = λ x → Q₁ x ⊎ Q₂ x 
    resp∪ : P∪ Respects _≈_  
    resp∪ eq (inj₁ x) = inj₁ (resp₁ eq x)
    resp∪ eq (inj₂ y) = inj₂ (resp₂ eq y)
    enum∪ : List A
    enum∪ = enum₁ ++ enum₂
    isEnum∪ : IsEnumeration S enum∪ P∪
    isEnum∪ (x , inj₁ y) =
      let x∈e1 = isEnum₁ (x , y)
      in ∈-++⁺ˡ S enum₁ x∈e1
    isEnum∪ (x , inj₂ y) =
      let x∈e2 = isEnum₂ (x , y)
      in ∈-++⁺ʳ S x∈e2

    _∪_ : FinPred S
    _∪_ = record
      { P = P∪
      ; resp = resp∪
      ; enum = enum∪ 
      ; isEnum = isEnum∪
      }

  module _  (P : FinPred S) where
    open FinPred P renaming (P to P')

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
