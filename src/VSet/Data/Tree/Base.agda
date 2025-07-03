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
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat

open import VSet.Path

infix 30 _⊻_

data Tree : Type where
  ◎ : Tree
  _⊻_ : Tree → Tree → Tree

caseTree : ∀ {ℓ} → {A : Type ℓ} → (al af : A) → Tree → A
caseTree al af ◎ = al
caseTree al af (t1 ⊻ t2) = af

⊻≢◎ : {t1 t2 : Tree} → t1 ⊻ t2 ≢ ◎
⊻≢◎ {t1} {t2} f≡l = subst (caseTree ⊥ Tree) f≡l ◎

◎≢⊻ : {t1 t2 : Tree} → ◎ ≢ t1 ⊻ t2 
◎≢⊻ {t1} {t2} f≡l = subst (caseTree Tree ⊥) f≡l ◎ 

∥_∥ : Tree → ℕ
∥ ◎ ∥ = 1
∥ t1 ⊻ t2 ∥ = (∥ t1 ∥) + (∥ t2 ∥)

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

module SmallStepInductive where
  data _▻_ : Tree → Tree → Type where
    α : (A B C : Tree) → ((A ⊻ B) ⊻ C) ▻ (A ⊻ (B ⊻ C))
    cong-left : (A A' B : Tree) → A ▻ A' → (A ⊻ B) ▻ (A' ⊻ B)
    cong-right : (A B B' : Tree) → B ▻ B' → (A ⊻ B) ▻ (A ⊻ B')

  data _▻*_ : Tree → Tree → Type where
    [] : {A : Tree} → A ▻* A
    _∷_ : {A B C : Tree} → A ▻ B → B ▻* C → A ▻* C

  _▻⁺_ : Tree → Tree → Type
  A ▻⁺ B = Σ[ δ ∈ A ▻* B ] ((p : A ≡ B) → (subst (_▻* B) p δ) ≢ [])
  
  ▻-preserves-size : ∀ {X Y} → X ▻ Y → ∥ X ∥ ≡ ∥ Y ∥
  ▻-preserves-size {X} {Y} (α A B C) = {!+n-assoc!}
  ▻-preserves-size {X} {Y} (cong-left A A' B step) = {!!}
  ▻-preserves-size {X} {Y} (cong-right A B B' step) = {!!}

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

  -- Trivial lemmas
  ◎¬α-left : {A : Tree} → ¬ α ◎ A
  ◎¬α-left {A} ()
  ◎¬α-right : {A : Tree} → ¬ α A ◎
  ◎¬α-right {◎ ⊻ _} ()
  ◎¬α-right {(_ ⊻ _) ⊻ _} ()

  ◎⊻¬α-left : {A B : Tree} → ¬ α (◎ ⊻ A) B
  ◎⊻¬α-left {◎} {_} α' = α'
  ◎⊻¬α-left {_ ⊻ _} {_} α' = α'
  ◎⊻¬α-right : {A B : Tree} → ¬ α A (B ⊻ ◎)
  ◎⊻¬α-right {◎ ⊻ _} {◎} α' = α'
  ◎⊻¬α-right {(_ ⊻ _) ⊻ _} {◎} α' = α'
  ◎⊻¬α-right {◎ ⊻ _} {_ ⊻ _} α' = α'
  ◎⊻¬α-right {(_ ⊻ _) ⊻ _} {_ ⊻ _} α' = α'

  ¬◎≪ : {A B : Tree} → ¬ ◎ ≪ (A ⊻ B)
  ¬◎≪ {A} (inl eq) = ◎≢⊻ eq
  ¬◎≪ {A} (inr (inl ()))
  ¬◎≪ {A} (inr (inr ()))
  ¬≪◎ : {A B : Tree} → ¬ (A ⊻ B) ≪ ◎
  ¬≪◎ {A} (inl eq) = ⊻≢◎ eq
  ¬≪◎ {A} (inr (inl α')) = ◎¬α-right α'

  ≪'-acc : {X Y : Tree} → Y ≪' X → Acc _≪'_ Y
  ≪'-acc {_} {_} (inl eq , ne) = absurd (ne eq)
  ≪'-acc {A ⊻ (B ⊻ C)} {(D ⊻ E) ⊻ F} (inr (inl α') , ne)
    -- This should be a single atomic swap, but I'm not sure how to
    -- split this up so it terminates.
    = acc λ X less → ≪'-acc less
  ≪'-acc {A ⊻ (B ⊻ C)} {(D ⊻ E) ⊻ F} (inr (inr x) , ne) = {!!}
  ≪'-acc {◎} {◎} (inr _ , ne) = absurd (ne refl)
  ≪'-acc {◎} {_ ⊻ _} (inr (inl α') , _) = absurd (◎¬α-right α')
  ≪'-acc {_ ⊻ _} {◎} (inr (inl ()) , ne)
  ≪'-acc {_ ⊻ _} {◎} (inr (inr ()) , ne)
  ≪'-acc {◎ ⊻ C} {◎ ⊻ F} (inr (inr x) , ne) = {!!}
  ≪'-acc {◎ ⊻ C} {(D ⊻ D₁) ⊻ F} x = {!!}
  ≪'-acc {(A ⊻ A₁) ⊻ C} {D ⊻ F} x = {!!}
    where
      wfrec : {A : Tree} → WFRec _≪'_ (Acc _≪'_) A
      wfrec = {!!}

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
