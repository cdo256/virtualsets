module VirtualSet where

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

private
  variable
    c ℓ : Level.Level
