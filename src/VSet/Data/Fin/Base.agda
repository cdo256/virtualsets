module VSet.Data.Fin.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Nat

Fin : ℕ → Type
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

module Tree (x : ℕ) where

  Fin→ℕ : {x : ℕ} → Fin x → ℕ
  Fin→ℕ {suc x} (inl _) = zero
  Fin→ℕ {suc x} (inr a) = suc (Fin→ℕ a)

  ℕ→Fin : (x : ℕ) → Fin (suc x)
  ℕ→Fin = ?

  _+ꟳ_ : {x : ℕ} → Fin → Fin 

  inv : {x : ℕ} → (y : Fin x) → (a : Fin y) → Σ[ b ∈ Fin y ] (a +ꟳ b ≡ y)
  inv = ?

  Tree : {x : ℕ} → (y : Fin x) → Type
  TreeSplit : {x : ℕ} → (a : Fin x) → Tree a → Tree (inv x a)
  Tree zero = ⊤
  Tree (suc n) = Σ (Fin n) {!!}


  -- data Tree : Type where
  --   Leaf : Tree
  --   Fork : Tree → Tree → Tree
