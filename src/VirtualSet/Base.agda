module VirtualSet.Base where

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

open import Data.Fin
  using (Fin) renaming (zero to zeroF; suc to sucF)
open import Data.Nat.Properties
  using (+-commutative)
open import Data.Nat
  using (ℕ)
  renaming (zero to zeroℕ; suc to sucℕ; _+_ to _+ℕ_)

private
  variable
    c ℓ : Level.Level
  
_-A : {l m n : ℕ} (f : Fin (l +ℕ n) → Fin (m +ℕ n)) → Fin l → Fin m
_-A {n = zeroℕ} f a rewrite (+-commutative ? ?) = {!f a!}
_-A {n = sucℕ n} f a = {!!}
