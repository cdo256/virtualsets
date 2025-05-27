module FiniteSetoid where

open import Data.Nat
  hiding (_⊔_; _+_)
import Data.List
open Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional
  hiding (_∈_)
open import Data.Product
open import Relation.Binary.Bundles
open import Relation.Binary.Structures
  using (IsEquivalence)
open import Level
  using (_⊔_; 0ℓ; Lift; lift)
  renaming (suc to lsuc)
open import Data.Empty
open import Data.Sum.Base
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)
import Data.Sum.Relation.Binary.Pointwise
open import Data.List.Relation.Unary.Enumerates.Setoid
--  using (Pointwise)

private
  variable
    c ℓ : Level.Level

module _ (S : Setoid c ℓ) where
  open Setoid S
    renaming (Carrier to A)
  open import Data.List.Membership.Setoid S

  IsFiniteSetoid : Set (c ⊔ ℓ)
  IsFiniteSetoid =  Σ[ xs ∈ List A ] IsEnumeration S xs

record FiniteSetoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  open Setoid
  field
    S : Setoid c ℓ
    enum : List (Carrier S)
    isEnum : IsEnumeration S enum 

emptySetoid : Setoid 0ℓ 0ℓ
emptySetoid = record
  { Carrier = ⊥
  ; _≈_ = _
  ; isEquivalence =  _
  }

emptyFiniteSetoid : FiniteSetoid 0ℓ 0ℓ
emptyFiniteSetoid = record
  { setoid = emptySetoid
  ; enum = []
  ; isEnum = λ ()
  }

module _ (S : FiniteSetoid c ℓ) (T : FiniteSetoid c ℓ) where
  open FiniteSetoid S using () renaming (S to S'; isFinite to SFinite)
  open FiniteSetoid T using () renaming (S to T'; isFinite to TFinite)
  open Setoid S' using ()
    renaming (Carrier to A; _≈_ to _≈₁_; isEquivalence to equiv₁)
  open Setoid T' using ()
    renaming (Carrier to B; _≈_ to _≈₂_; isEquivalence to equiv₂)

  open Data.Sum.Relation.Binary.Pointwise
      using (Pointwise; ⊎-isEquivalence; _⊎ₛ_)
  open import Data.List.Membership.Propositional.Properties
      using (∈-++⁺ˡ)
  open import Data.List.Membership.Setoid (S' ⊎ₛ T')
    using (_∈_)

  enum : List (A ⊎ B)
  enum = ?
  isEnum : IsEnumeration (S' ⊎ₛ T') enum
  isEnum = ?
  
  plus : FiniteSetoid _ _
  plus = record
    { setoid = S' ⊎ₛ T'
    ; enum = ?
    ; isEnum = ?
    }

-- _+_ : FiniteSetoid c ℓ → FiniteSetoid c ℓ → FiniteSetoid c ℓ
-- _+_ = plus
