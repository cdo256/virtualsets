module VSet.Data.SumTree.WellFounded where

open import VSet.Prelude
open import VSet.Data.Nat hiding (_<_)
open import VSet.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.SumTree.Base
open import VSet.Data.SumTree.Metrics
open import VSet.Data.Nat.WellFounded
open import Cubical.Data.Nat.Order
open import Cubical.Induction.WellFounded
open import Data.Product.Relation.Binary.Lex.Strict 
open import Relation.Binary.Core

private
  variable
    ℓ ℓ' : Level

{-
acc' : {A B : ℕ × ℕ} → B ≺' A → Acc _≺'_ B
acc' {a1 , a2} {b1 , b2} (inl b1<a1) = {!!}
acc' {a1 , a2} {b1 , b2} (inr (b1≡a1 , b2<a2)) = {!!}

-- _≺_ : Tree ℕΣM ΣM ΣM  → Tree ℕ → Type
-- A ≺ B with Σ∥ A ∥ ≟ Σ∥ B ∥
-- ... | lt _ = ⊤
-- ... | eq _ = #∥ A ∥ < #∥ B ∥
-- ... | gt _ = ⊥



-- acc' : {A B : Tree ℕ} → B ≺ A → Acc _≺_ B
-- acc' {A} {B} B≺A with Σ∥ A ∥ ≟ Σ∥ B ∥
-- ... | lt _ = {!!}
-- ... | eq _ = {!#∥ A ∥ < #∥ B ∥!}
-- ... | gt _ = {!!}

-- rec' = WFRec _≺_ {!!} {!!}
-}
