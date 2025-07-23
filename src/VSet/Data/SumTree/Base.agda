module VSet.Data.SumTree.Base where

open import VSet.Prelude
open import VSet.Data.Nat hiding (_+_; _<_)
open import VSet.Data.SomeFin.Base
open import Cubical.Data.Nat.Order

infix 30 _＋_

private
  variable
    ℓ ℓ' : Level

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
map f ⟨ X ⟩ₜ = ⟨ f X ⟩ₜ
map f (x ＋ y) = map f x ＋ map f y

-- Make sum type from Tree
[_]ₛ : Tree (Type ℓ) → Type ℓ
[ ⟨ X ⟩ₜ ]ₛ = X
[ l ＋ r ]ₛ = [ l ]ₛ ⊎ [ r ]ₛ

-- Fin tree
⟦_⟧ₛ : Tree ℕ → Type
⟦_⟧ₛ = [_]ₛ ∘ map ⟦_⟧

ftree : ℕ → Tree ⊤
ftree zero = ⟨ tt ⟩ₜ
ftree (suc x) = ⟨ tt ⟩ₜ ＋ ftree x

module _ {A B C : Tree (Type ℓ) } where
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
