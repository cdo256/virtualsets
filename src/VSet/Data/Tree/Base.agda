module VSet.Data.Tree.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives

open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
-- open import Cubical.Data.Nat
-- open import Cubical.Data.Nat.Order

open import VSet.Data.NatPlus.Base

data Tree : Type where
  leaf : Tree
  fork : Tree → Tree → Tree

infix 30 ⟦_⟧ ∥_∥

⟦_⟧ : Tree → Type
⟦ leaf ⟧ = ⊤
⟦ fork t1 t2 ⟧ = ⟦ t1 ⟧ ⊎ ⟦ t2 ⟧

∥_∥ : Tree → ℕ+
∥ leaf ∥ = one
∥ fork t1 t2 ∥ = ∥ t1 ∥ + ∥ t2 ∥

Tree# : ℕ+ → Type
Tree# n = Σ[ t ∈ Tree ] (∥ t ∥ ≡ n)

ftree : ℕ+ → Tree
ftree one = leaf
ftree (suc x) = {!fork leaf (ftree x)!}
