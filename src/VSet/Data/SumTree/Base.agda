module VSet.Data.SumTree.Base where

open import VSet.Prelude
open import VSet.Data.Nat hiding (_+_)
open import VSet.Data.SomeFin.Base

open import Cubical.Data.Bool
open import Cubical.Foundations.Isomorphism
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary

infix 30 _＋_

private
  variable
    ℓ ℓ' : Level
    A : Type

data Tree {ℓ} (A : Type ℓ) : Type ℓ where
  ⟨_⟩ₜ : A → Tree A
  _＋_ : Tree A → Tree A → Tree A

case : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (al af : B) → Tree A → B
case al af ⟨ x ⟩ₜ = al
case al af (t1 ＋ t2) = af

fold : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
     → (al : A → B) (af : B → B → B) → Tree A → B
fold al af ⟨ x ⟩ₜ = al x
fold al af (t1 ＋ t2) = af (fold al af t1) (fold al af t2)

fork≢leaf : ∀ {ℓ} {A : Type ℓ} (t1 t2 : Tree A) (x : A) → t1 ＋ t2 ≢ ⟨ x ⟩ₜ
fork≢leaf {ℓ = ℓ} {A = A} t1 t2 x f≡l =
  lower (subst (case {B = Type ℓ} ⊥* (Tree A)) f≡l (t1 ＋ t2))

leaf≢fork : ∀ {ℓ} {A : Type ℓ} (t1 t2 : Tree A) (x : A) → ⟨ x ⟩ₜ ≢ t1 ＋ t2
leaf≢fork {ℓ = ℓ} {A = A} t1 t2 x l≡f =
  lower (subst (case {B = Type ℓ} (Tree A) ⊥*) l≡f ⟨ x ⟩ₜ)


map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (f : A → B) → Tree A → Tree B
map f = fold (λ x → ⟨ f x ⟩ₜ) _＋_

∥_∥ₜ : Tree ℕ → ℕ
∥ ⟨ x ⟩ₜ ∥ₜ = 1
∥ t1 ＋ t2 ∥ₜ = (∥ t1 ∥ₜ) + (∥ t2 ∥ₜ)

[_]ₛ : Tree (Type ℓ) → Type ℓ
[ ⟨ X ⟩ₜ ]ₛ = X
[ l ＋ r ]ₛ = [ l ]ₛ ⊎ [ r ]ₛ

⟦_⟧ₛ : Tree ℕ → Type
⟦_⟧ₛ = [_]ₛ ∘ map ⟦_⟧

Tree# : ℕ → Type
Tree# n = Σ[ t ∈ Tree ℕ ] (∥ t ∥ₜ ≡ suc n)

ftree : ℕ → Tree ⊤
ftree zero = ⟨ tt ⟩ₜ
ftree (suc x) = ⟨ tt ⟩ₜ ＋ ftree x

module _ {D : Type ℓ} {A B C : Tree (Type ℓ) } where
  α : [ A ＋ (B ＋ C) ]ₛ → [ (A ＋ B) ＋ C ]ₛ
  α (inl x) = inl (inl x)
  α (inr (inl x)) = inl (inr x)
  α (inr (inr x)) = inr x

  α⁻¹ : [ (A ＋ B) ＋ C ]ₛ → [ A ＋ (B ＋ C) ]ₛ
  α⁻¹ (inl (inl x)) = inl x
  α⁻¹ (inl (inr x)) = inr (inl x)
  α⁻¹ (inr x) = inr (inr x)

  αIso : Iso [ A ＋ (B ＋ C) ]ₛ [ (A ＋ B) ＋ C ]ₛ
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


{-

αEquiv : {A B C : Tree} → ⟦ A ⊻ (B ⊻ C) ⟧ ≃ ⟦ (A ⊻ B) ⊻ C ⟧ 
αEquiv = isoToEquiv αIso


α∥_∥ : (B : Tree) → (x : ⟦ B ⟧) → ⟦ T∥ B ∥ ⟧
α∥ (leaf x) ∥ tt with inspect (λ B → ⟦ T∥ B ∥ ⟧)
... | X = {!subst {!!} {!!} {!!}!}
α∥ A ⊻ B ∥ x = {!!}

reassoc : {A B : Tree} → ∥ A ∥ ≡ ∥ B ∥ → Iso ⟦ A ⟧ ⟦ B ⟧
reassoc {(leaf x)} {(leaf x)} p = {!?!}
reassoc {(leaf x)} {B₁ ⊻ B₂} p = {!!}
reassoc {A₁ ⊻ A₂} {(leaf x)} p = {!!}
reassoc {A₁ ⊻ A₂} {B₁ ⊻ B₂} p = {!!}

-- -}
-- -}
-- -}
