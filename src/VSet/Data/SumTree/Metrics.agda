module VSet.Data.SumTree.Metrics where

open import VSet.Prelude
open import VSet.Data.Nat hiding (_+_; _<_)
open import VSet.Data.SomeFin.Base
open import Cubical.Data.Nat.Order
open import VSet.Data.SumTree.Base

private
  variable
    ℓ ℓ' : Level

-- Sum of leaves
Σ∥_∥ : Tree ℕ → ℕ
Σ∥ ⟨ X ⟩ₜ ∥ = X
Σ∥ A ＋ B ∥ = Σ∥ A ∥ + Σ∥ B ∥

-- Number of zero leaves
0∥_∥ : Tree ℕ → ℕ
0∥ ⟨ zero ⟩ₜ ∥ = 1
0∥ ⟨ suc _ ⟩ₜ ∥ = 0
0∥ A ＋ B ∥ = 0∥ A ∥ + 0∥ B ∥

-- Number of nodes
#∥_∥ : Tree ℕ → ℕ
#∥ ⟨ _ ⟩ₜ ∥ = 1
#∥ A ＋ B ∥ = #∥ A ∥ + #∥ B ∥

-- Refinement types
TreeΣ[_] : ℕ → Type
TreeΣ[ n ] = Σ[ A ∈ Tree ℕ ] (Σ∥ A ∥ ≡ n)
TreeΣ+ : Type
TreeΣ+ = Σ[ A ∈ Tree ℕ ] (Σ∥ A ∥ ≥ 1)
Tree0[_] : ℕ → Type
Tree0[ n ] = Σ[ A ∈ Tree ℕ ] (Σ∥ A ∥ ≡ n)
Tree0+ : Type
Tree0+ = Σ[ A ∈ Tree ℕ ] (0∥ A ∥ ≥ 1)
Tree∖0 : Type
Tree∖0 = Tree0[ 0 ]

record TreeMetrics : Type where
  constructor _,_
  field
    ΣM : ℕ
    #M : ℕ

open TreeMetrics

metrics : Tree ℕ → TreeMetrics
metrics A = Σ∥ A ∥ , #∥ A ∥

data _≺M_ : (AM BM : TreeMetrics) → Type where
  Σ<Σ : ∀ {AM BM} → ΣM AM < ΣM BM → AM ≺M BM 
  #<# : ∀ {AM BM} → ΣM AM ≡ ΣM BM → #M AM < #M BM → AM ≺M BM
