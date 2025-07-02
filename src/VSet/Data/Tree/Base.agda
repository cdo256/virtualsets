module VSet.Data.Tree.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Cubical.Core.Primitives

open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism

open import Induction.WellFounded

open import VSet.Data.NatPlus.Base

data Tree : Type where
  ◎ : Tree
  _⊻_ : Tree → Tree → Tree

bubbleOne : Tree → Tree → Tree
bubbleOne ◎ R = R
bubbleOne (A ⊻ B) R = bubbleOne A (B ⊻ R)

norm : Tree → Tree
norm ◎ = ◎
norm (A ⊻ B) = ◎ ⊻ norm (bubbleOne A B)

{-

infix 30 ⟦_⟧ ∥_∥

⟦_⟧ : Tree → Type
⟦ ◎ ⟧ = ⊤
⟦ t1 ⊻ t2 ⟧ = ⟦ t1 ⟧ ⊎ ⟦ t2 ⟧

∥_∥ : Tree → ℕ+
∥ ◎ ∥ = one
∥ t1 ⊻ t2 ∥ = ∥ t1 ∥ + ∥ t2 ∥

Tree# : ℕ+ → Type
Tree# n = Σ[ t ∈ Tree ] (∥ t ∥ ≡ n)

ftree : ℕ+ → Tree
ftree one = ◎
ftree (suc x) = ◎ ⊻ (ftree x)



α : {A B C : Tree} → ⟦ A ⊻ (B ⊻ C) ⟧ → ⟦ (A ⊻ B) ⊻ C ⟧
α (inl x) = inl (inl x)
α (inr (inl x)) = inl (inr x)
α (inr (inr x)) = inr x

α⁻¹ : {A B C : Tree} → ⟦ (A ⊻ B) ⊻ C ⟧ → ⟦ A ⊻ (B ⊻ C) ⟧
α⁻¹ (inl (inl x)) = inl x
α⁻¹ (inl (inr x)) = inr (inl x)
α⁻¹ (inr x) = inr (inr x)

αIso : {A B C : Tree} → Iso ⟦ A ⊻ (B ⊻ C) ⟧ ⟦ (A ⊻ B) ⊻ C ⟧
αIso = iso α α⁻¹ sect retr
  where
    sect : section α α⁻¹
    sect (inl (inl x)) = refl
    sect (inl (inr x)) = refl
    sect (inr x) = refl
    retr : retract α α⁻¹ 
    retr (inl x) = refl
    retr (inr (inl x)) = refl
    retr (inr (inr x)) = refl

αEquiv : {A B C : Tree} → ⟦ A ⊻ (B ⊻ C) ⟧ ≃ ⟦ (A ⊻ B) ⊻ C ⟧ 
αEquiv = isoToEquiv αIso


α∥_∥ : (B : Tree) → (x : ⟦ B ⟧) → ⟦ T∥ B ∥ ⟧
α∥ ◎ ∥ tt with inspect (λ B → ⟦ T∥ B ∥ ⟧)
... | X = {!subst {!!} {!!} {!!}!}
α∥ A ⊻ B ∥ x = {!!}

reassoc : {A B : Tree} → ∥ A ∥ ≡ ∥ B ∥ → Iso ⟦ A ⟧ ⟦ B ⟧
reassoc {◎} {◎} p = {!?!}
reassoc {◎} {B₁ ⊻ B₂} p = {!!}
reassoc {A₁ ⊻ A₂} {◎} p = {!!}
reassoc {A₁ ⊻ A₂} {B₁ ⊻ B₂} p = {!!}
-}
