```
module Notes.UnsolvedMetas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sum
open import Cubical.Data.Fin
open import Cubical.Data.Nat

private
  variable
    ℓ : Level
    D : Type ℓ

data Tree : Type where
  leaf : ℕ → Tree
  _&_ : Tree → Tree → Tree

⟦_⟧ : Tree → Type
⟦ leaf x ⟧ = Fin x
⟦ x & y ⟧ = ⟦ x ⟧ ⊎ ⟦ y ⟧

-- α : {A B C : Type ℓ} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
-- α (inl x) = inl (inl x)
-- α (inr (inl x)) = inl (inr x)
-- α (inr (inr x)) = inr x

-- α⁻¹ : {A B C : Type ℓ} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
-- α⁻¹ (inl (inl x)) = inl x
-- α⁻¹ (inl (inr x)) = inr (inl x)
-- α⁻¹ (inr x) = inr (inr x)

-- αIso : {A B C : Type ℓ} → Iso (A ⊎ (B ⊎ C)) ((A ⊎ B) ⊎ C)
-- αIso = iso α α⁻¹ sect retr
--   where
--     sect : section α α⁻¹
--     sect (inl (inl x)) = refl
--     sect (inl (inr x)) = refl
--     sect (inr x) = refl
--     retr : retract α α⁻¹ 
--     retr (inl x) = refl
--     retr (inr (inl x)) = refl
--     retr (inr (inr x)) = refl




-- α : {A B C : ℕ} → ⟦ leaf A & (leaf B & leaf C) ⟧ → ⟦ (leaf A & leaf B) & leaf C ⟧
-- α (inl x) = inl (inl x)
-- α (inr (inl x)) = inl (inr x)
-- α (inr (inr x)) = inr x

-- α⁻¹ : {A B C : ℕ} → ⟦ (leaf A & leaf B) & leaf C ⟧ → ⟦ leaf A & (leaf B & leaf C) ⟧
-- α⁻¹ (inl (inl x)) = inl x
-- α⁻¹ (inl (inr x)) = inr (inl x)
-- α⁻¹ (inr x) = inr (inr x)

-- αIso : {A B C : ℕ} → Iso ⟦ (leaf A & (leaf B & leaf C)) ⟧ ⟦ ((leaf A & leaf B) & leaf C) ⟧
-- αIso = iso α α⁻¹ sect retr
--   where
--     sect : section α α⁻¹
--     sect (inl (inl x)) = refl
--     sect (inl (inr x)) = refl
--     sect (inr x) = refl
--     retr : retract α α⁻¹ 
--     retr (inl x) = refl
--     retr (inr (inl x)) = refl
--     retr (inr (inr x)) = refl

α : {A B C : Tree} → ⟦ A & (B & C) ⟧ → ⟦ (A & B) & C ⟧
α (inl x) = inl (inl x)
α (inr (inl x)) = inl (inr x)
α (inr (inr x)) = inr x

α⁻¹ : {A B C : Tree} → ⟦ (A & B) & C ⟧ → ⟦ A & (B & C) ⟧
α⁻¹ (inl (inl x)) = inl x
α⁻¹ (inl (inr x)) = inr (inl x)
α⁻¹ (inr x) = inr (inr x)

αIso : {A B C : Tree} → Iso ⟦ (A & (B & C)) ⟧ ⟦ ((A & B) & C) ⟧
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


α : {A B C : Tree} → ⟦ A & (B & C) ⟧ → ⟦ (A & B) & C ⟧
α (inl x) = inl (inl x)
α (inr (inl x)) = inl (inr x)
α (inr (inr x)) = inr x

α⁻¹ : {A B C : Tree} → ⟦ (A & B) & C ⟧ → ⟦ A & (B & C) ⟧
α⁻¹ (inl (inl x)) = inl x
α⁻¹ (inl (inr x)) = inr (inl x)
α⁻¹ (inr x) = inr (inr x)

αIso : {A B C : Tree} → Iso ⟦ (A & (B & C)) ⟧ ⟦ ((A & B) & C) ⟧
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

```
