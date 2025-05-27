module FiniteSetoid where

open import Data.Empty using (⊥) 
open import Data.List using (List; []; _∷_) 
open import Data.List.Relation.Unary.Enumerates.Setoid using (IsEnumeration) 
open import Data.Product using (Σ-syntax) 
open import Data.Sum.Base using (_⊎_) 
open import Data.Sum.Relation.Binary.Pointwise using () 
open import Level using (_⊔_; 0ℓ; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.Bundles using (Setoid) 
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)

private
  variable
    c ℓ : Level.Level

module _ (S : Setoid c ℓ) where
  open Setoid S using () 
    renaming (Carrier to A)
  open import Data.List.Membership.Setoid S using () 

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
  { S = emptySetoid
  ; enum = []
  ; isEnum = λ ()
  }

module _ (S₁ : FiniteSetoid c ℓ) (S₂ : FiniteSetoid c ℓ) where
  open FiniteSetoid S₁ using ()
    renaming (S to T₁; enum to enum₁; isEnum to isEnum₁)
  open FiniteSetoid S₂ using ()
    renaming (S to T₂; enum to enum₂; isEnum to isEnum₂)
  open Setoid T₂ using ()
    renaming (Carrier to A₁; _≈_ to _≈₁_; isEquivalence to equiv₁)
  open Setoid T₁ using ()
    renaming (Carrier to A₂; _≈_ to _≈₂_; isEquivalence to equiv₂)

  open Data.Sum.Relation.Binary.Pointwise
      using (Pointwise; ⊎-isEquivalence; _⊎ₛ_)
  open import Data.List.Membership.Propositional.Properties
      using (∈-++⁺ˡ)
  open import Data.List.Membership.Setoid (T₁ ⊎ₛ T₂)
    using (_∈_)
  open import Data.List.Base using () 

  enum : List (A₁ ⊎ A₂)
  enum = {!map inj₁ enum₁ ++ map inj₂ enum₂!}
  -- isEnum : IsEnumeration (T₁ ⊎ₛ T₂) enum
  -- isEnum = {!!}
  
  plus : FiniteSetoid _ _
  plus = record
    { S = T₁ ⊎ₛ T₂
    ; enum = {!!}
    ; isEnum = {!!}
    }

-- _+_ : FiniteSetoid c ℓ → FiniteSetoid c ℓ → FiniteSetoid c ℓ
-- _+_ = plus
