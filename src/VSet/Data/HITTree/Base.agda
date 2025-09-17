module VSet.Data.HITTree.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Cubical.Core.Primitives

open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary

open import Cubical.Data.Maybe
open import Cubical.Data.Nat

open import VSet.Path

data BitTree : Type where
  𝟘 : BitTree 
  𝟙 : BitTree
  _⊕_ : (A B : BitTree) → BitTree

data BinTree : Type where
  𝟙 : BinTree
  _⊕_ : (A B : BinTree) → BinTree

-- Normal means no 𝟘 except if it's at the root.
normal : BitTree → Type
normal 𝟘 = ⊤ 
normal A = f A 
  where
    f : BitTree → Type
    f 𝟘 = ⊥
    f 𝟙 = ⊤ 
    f (A ⊕ B) = normal A × normal B

∥_∥ : BitTree → ℕ
∥ 𝟘 ∥ = 0 
∥ 𝟙 ∥ = 1
∥ t1 ⊕ t2 ∥ = (∥ t1 ∥) + (∥ t2 ∥)

module Bit→Bin where
  join : Maybe BinTree → Maybe BinTree → Maybe BinTree
  join nothing B = B
  join (just A) nothing = just A
  join (just A) (just B) = just (A ⊕ B)

  f : BitTree → Maybe BinTree
  f 𝟘 = nothing
  f 𝟙 = just 𝟙
  f (A ⊕ B) = join (f A) (f B)



norm : BitTree → BitTree
norm = {!!}

data HITTree : Type where
  《_》 : BitTree → HITTree
  α : ∀ {A B C : BitTree} → 《 (A ⊕ B) ⊕ C 》 ≡ 《 A ⊕ (B ⊕ C) 》
  δₗ : ∀ {A : BitTree} → 《 𝟘 ⊕ A 》 ≡ 《 A 》
  δᵣ : ∀ {A : BitTree} → 《 A ⊕ 𝟘 》 ≡ 《 A 》


⟦_⟧ : BitTree → Type
⟦ 𝟘 ⟧ = ⊥
⟦ 𝟙 ⟧ = ⊤
⟦ A ⊕ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
