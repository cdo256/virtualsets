module FiniteSetoid where

open import Data.Nat
  hiding (_⊔_; _+_)
import Data.List
open Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional
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
open import Data.Sum.Relation.Binary.Pointwise
  using (Pointwise)

private
  variable
    c ℓ : Level.Level

module _ (S : Setoid c ℓ) where
  open Setoid S
    renaming (Carrier to A)

  AllIn : (xs : List (Setoid.Carrier S)) → Set (c ⊔ ℓ)
  AllIn xs = ∀ (a : A) → Σ[ b ∈ A ] a ≈ b × b ∈ xs 

  IsFiniteSetoid : Set (c ⊔ ℓ) 
  IsFiniteSetoid =  Σ[ xs ∈ List A ] AllIn xs

record FiniteSetoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  field
    setoid : Setoid c ℓ
    isFinite : IsFiniteSetoid setoid 

emptySetoid : Setoid 0ℓ 0ℓ
emptySetoid = record
  { Carrier = ⊥
  ; _≈_ = _
  ; isEquivalence =  _
  }

emptyFiniteSetoid : FiniteSetoid 0ℓ 0ℓ
emptyFiniteSetoid = record
  { setoid = emptySetoid
  ; isFinite = [] , λ () 
  }

module _ (S : FiniteSetoid c ℓ) (T : FiniteSetoid c ℓ) where
  open FiniteSetoid S using () renaming (setoid to S'; isFinite to SFinite)
  open FiniteSetoid T using () renaming (setoid to T'; isFinite to TFinite)
  open Setoid S' using ()
    renaming (Carrier to A; _≈_ to _≈₁_; isEquivalence to equiv₁)
  open Setoid T' using ()
    renaming (Carrier to B; _≈_ to _≈₂_; isEquivalence to equiv₂)

  private
    open IsEquivalence
    eq : A ⊎ B → A ⊎ B → Set ℓ
    eq (inj₁ x) (inj₁ y) = x ≈₁ y
    eq (inj₂ x) (inj₂ y) = x ≈₂ y
    eq _ _ = Lift ℓ ⊥
    refl' : Reflexive eq
    refl' {inj₁ x} = refl equiv₁
    refl' {inj₂ y} = refl equiv₂
    sym' : Symmetric eq
    sym' {inj₁ x} {inj₁ y} = sym equiv₁
    sym' {inj₂ x} {inj₂ y} = sym equiv₂
    -- sym' {_} {_} {!!}

    -- Failed to solve the following constraints:
    --   eq _i_145 _k_147 =< eq i k (blocked on _i_145)
    --   eq j k =< eq _j_146 _k_147 (blocked on _j_146)
    --   eq i j =< eq _i_145 _j_146 (blocked on _i_145)
    --   eq _y_142 _x_141 =< eq y x (blocked on _y_142)
    --   eq x y =< eq _x_141 _y_142 (blocked on _x_141)
    --   eq _x_138 _x_138 =< eq x x (blocked on _x_138)
    
    trans' : Transitive eq
    trans' {inj₁ x} {inj₁ y} {inj₁ z} = trans equiv₁
    trans' {inj₂ x} {inj₂ x₁} {inj₂ x₂} = trans equiv₂
    trans' {inj₁ x} {inj₁ y} {inj₂ z} xy ()
    trans' {inj₁ x} {inj₂ y} {inj₁ z} () ()
    trans' {inj₁ x} {inj₂ y} {inj₂ z} () yz
    trans' {inj₂ x} {inj₁ y} {inj₁ z} () yz
    trans' {inj₂ x} {inj₁ y} {inj₂ z} () ()
    trans' {inj₂ x} {inj₂ y} {inj₁ z} xy ()

    -- zs : List (A ⊎ B)
    -- zs = Data.List.map inj₁ (proj₁ SFinite) ++ Data.List.map inj₂ (proj₁ TFinite)
    
    -- ys, allIn₂ = TFinite

  plus : FiniteSetoid c ℓ
  plus = record
    { setoid = record
      { Carrier = A ⊎ B
      ; _≈_ = eq
      ; isEquivalence = record
        { refl = refl'
        ; sym = {!!}
        ; trans = trans'
        }
      }
    ; isFinite = {!!} , {!!}
    }

-- _+_ : FiniteSetoid c ℓ → FiniteSetoid c ℓ → FiniteSetoid c ℓ
-- _+_ = plus
