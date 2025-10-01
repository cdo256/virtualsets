-- Taken from stdlib 
module VSet.Relation.Definitions where

open import VSet.Prelude
open import Cubical.Relation.Binary.Base 

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

PropU : ∀ ℓ → Type (ℓ-suc ℓ) 
PropU ℓ = Σ (Type ℓ) isProp

SetU : ∀ ℓ → Type (ℓ-suc ℓ) 
SetU ℓ = Σ (Type ℓ) isSet

Subset : (S : Type ℓ) → Type _ 
Subset {ℓ = ℓ} S = Σ (S → Type) PropU (ℓ-suc ℓ)

Subset-isSet : (S : SetU ℓ) → isSet (Subset (S .fst))
Subset-isSet (X , isSetX) = isSetΠ λ x → {!!}

-- SubsetU : (S : SetU ℓ) → SetU _ 
-- SubsetU {ℓ = ℓ} S = fst S → PropU (ℓ-suc ℓ)

-- Range : {X : Type ℓ} {Y : SetU ℓ₁} → (f : X → fst Y) → Subset Y
-- Range {X = X} {Y = Y} f y = (Σ X (λ x → f x ≡ y)) , λ (x , p) (x' , p') → {!isSet!}

-- SubsetFun : {X Y : Type} → (f : X → Y) → (X' : Subset X) → (Y' : Subset Y) → (X' → ?)
