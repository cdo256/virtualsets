module VSet.Data.SumTree.WellFounded where

open import VSet.Prelude
open import VSet.Data.Nat hiding (_+_; _<_)
open import VSet.Data.Nat.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SumTree.Base
open import VSet.Data.SumTree.Metrics
open import Cubical.Data.Nat.Order
open import Cubical.Induction.WellFounded

private
  variable
    ℓ ℓ' : Level

ℕ-wellFounded : WellFounded _<_
ℕ-wellFounded A = acc (accℕ A)
  where
    accℕ : (A B : ℕ) → B < A → Acc _<_ B
    accℕ zero B B<0 = absurd {A = λ _ → Acc _<_ B} (x≮0 B B<0)
    accℕ (suc A) zero _ = acc (λ C C<0 → absurd {A = λ _ → Acc _<_ C} (x≮0 C C<0))
    accℕ (suc A) (suc B) B'<A' =
      acc (λ C C'≤B' → accℕ A C (≤-trans C'≤B' (pred-≤-pred B'<A')))

-- ℕ-wellFounded : WellFounded _<_
-- ℕ-wellFounded A = acc (accℕ A)
--   where
--     accℕ : (A B : ℕ) → B < A → Acc _<_ B
--     accℕ zero B B<0 = absurd {A = λ _ → Acc _<_ B} (x≮0 B B<0)
--     accℕ (suc A) zero _ = acc (λ C C<0 → absurd (x≮0 C C<0))
--     accℕ (suc A) (suc B) B'<A' =
--       let
--         a' : Acc _<_ B
--         a' = accℕ A B (pred-≤-pred B'<A')
--       in {!!}


{-
wf≺' : ∀ x → Acc _≺'_ x
wf≺' (m , n) = acc h
  where
    h : WFRec _≺'_ (Acc _≺'_) (m , n)
    h = {!!}
    helper : ∀ {y} → y ≺' (m , n) → Acc _≺'_ y
    helper = {!!}


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
