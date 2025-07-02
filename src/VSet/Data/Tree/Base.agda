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
open import Cubical.Induction.WellFounded

open import VSet.Path
open import VSet.Data.NatPlus.Base

data Tree : Type where
  ◎ : Tree
  _⊻_ : Tree → Tree → Tree

module SmallStep where
  α-base-type : Tree → Tree → Type
  α-base-type ((A ⊻ B) ⊻ C) (A' ⊻ (B' ⊻ C')) = (A ≡ A') × (B ≡ B') × (C ≡ C')
  α-base-type _ _ = ⊥

  infixl 10 _<_ _≪_

  _<_ : Tree → Tree → Type
  cong-type :  Tree → Tree → Type
  cong-type (A ⊻ B) (A' ⊻ B') =
      ((A < A') × (B ≡ B')) 
    ⊎ ((A ≡ A') × (B < B'))
  cong-type _ _ = ⊥ 

  A < B = (α-base-type A B) ⊎ (cong-type A B)

--  _<⁺_ : Tree → Tree → Type 
--  A <⁺ B = (A ≡ B) ⊎ (Σ[ C ∈ Tree ] (A <⁺ C × C < B))

module BigStep where
  _≪_ : Tree → Tree → Type

  α : Tree → Tree → Type
  α ((A ⊻ B) ⊻ C) (A' ⊻ (B' ⊻ C')) = (A ≪ A') × (B ≪ B') × (C ≪ C')
  α _ _ = ⊥

  c : Tree → Tree → Type
  c (A ⊻ B) (A' ⊻ B') = A ≪ A' × B ≪ B'
  c _ _ = ⊥

  A ≪ B = (A ≡ B) ⊎ ((α A B) ⊎ (c A B))

  _≪'_ : Tree → Tree → Type
  A ≪' B = (A ≪ B) × (A ≢ B)

  -- WTS ≪' is well-founded

  ≪'-acc : {X Y : Tree} → Y ≪' X → Acc _≪'_ Y
  ≪'-acc {◎} {◎} β = ?
  ≪'-acc {◎} {_ ⊻ _} β = ?
  ≪'-acc {A ⊻ B} {C ⊻ D} (less , ne) =
    acc {!λ Y β → ≪'-acc β!}
    where
      wfrec : {A : Tree} → WFRec _≪'_ (Acc _≪'_) A
      wfrec {◎ ⊻ B} (◎ ⊻ F) ((ne , α , c) , ne') = acc {!!}
      wfrec {◎ ⊻ B} ((E ⊻ E₁) ⊻ F) ((ne , α , c) , ne') = acc {!!}
      wfrec {(A ⊻ A₁) ⊻ B} (E ⊻ F) ((ne , α , c) , ne')
        = acc {!!}

  ≪'-WellFounded : WellFounded _≪'_
  ≪'-WellFounded A = {!!}

{-

-- data TreeSwap : Type where
--   α : (A B C : Tree) → TreeSwap -- ((A ⊻ B) ⊻ C) ~ (A ⊻ (B ⊻ C))
--   cong-left : (A B : Tree) (S : TreeSwap A B)

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

-- -}
-- -}
-- -}
