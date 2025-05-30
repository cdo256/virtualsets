module VirtualSetoid where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Relation.Unary.Enumerates.Setoid
  using (IsEnumeration)
open import Data.List.Relation.Unary.Enumerates.Setoid.Properties
  using (++⁺)
open import Data.Product using (Σ-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using ()
open import Level using (_⊔_; 0ℓ; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Function.Bundles using (Func; Surjection; Injection)

open import FiniteSetoid using (FiniteSetoid; _+_)

private
  variable
    c ℓ : Level.Level
    X Y A B : FiniteSetoid c ℓ

module _ {X Y Z : FiniteSetoid c ℓ} where
  X' = FiniteSetoid.S X
  Y' = FiniteSetoid.S Y
  Z' = FiniteSetoid.S Z

  f : (Y : FiniteSetoid c ℓ) → (S : Fun  → Set _) → Set _ 
  
-- _-_ : Func X' Y' → Injection Z' X' → Func 
    
    

-- _-_ : (f : Func X Y) → (A : FiniteSetoid c ℓ) → X → Y
-- f - A = ?


open import Data.Nat
  hiding (_⊔_)
open import Data.Fin
open import Data.List
open import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional
open import Data.Product
open import Relation.Binary.Bundles
open import Level
  using (_⊔_; 0ℓ)
  renaming (suc to lsuc)
open import Data.Empty

