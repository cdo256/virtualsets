module VSet.Data.SumTree.Metrics where

open import VSet.Prelude
open import VSet.Data.Nat hiding (_<_)
open import VSet.Data.Fin.Base
open import Cubical.Data.Nat.Order
open import VSet.Data.Nat.WellFounded
open import VSet.Data.SumTree.Base
open import Cubical.Relation.Binary.Base 
open import Cubical.Induction.WellFounded
open import VSet.Function.Base
open import VSet.Relation.Definitions
open import VSet.Relation.WellFounded.Base
open import Cubical.Relation.Nullary.DecidablePropositions 

private
  variable
    ℓ ℓ' : Level

-- Sum of leaves
Σ∥_∥ : Tree ℕ → ℕ
Σ∥ ⟨ X ⟩ₜ ∥ = X
Σ∥ A ＋ B ∥ = Σ∥ A ∥ + Σ∥ B ∥

forkℕ : {A : Type ℓ} → A → A → ℕ → A
forkℕ az as zero = az
forkℕ az as (suc _) = as

-- Number of steps to deflate on the left
0L∥_∥ : Tree ℕ → ℕ
0L∥ ⟨ zero ⟩ₜ ∥ = 0
0L∥ ⟨ suc _ ⟩ₜ ∥ = 0
0L∥ A ＋ B ∥ = forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥

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
DeflatedTree : Type
DeflatedTree = Σ[ A ∈ Tree ℕ ] (0L∥ A ∥ ≡ 0)

metrics : Tree ℕ → ℕ × ℕ
metrics A = Σ∥ A ∥ , #∥ A ∥

_≺ₘ_ : Rel (Tree ℕ) (Tree ℕ) lzero
_≺ₘ_  = mapRel metrics _≺²_

≺ₘ-wellFounded : WellFounded _≺ₘ_
≺ₘ-wellFounded = mapRel-wellFounded metrics _≺²_ ℕ²-wellFounded

_≺₀ₗ_ : Rel (Tree ℕ) (Tree ℕ) lzero
_≺₀ₗ_ = mapRel 0L∥_∥ _<_

≺₀ₗ-wellFounded : WellFounded _≺₀ₗ_
≺₀ₗ-wellFounded = mapRel-wellFounded 0L∥_∥ _<_ ℕ-wellFounded
