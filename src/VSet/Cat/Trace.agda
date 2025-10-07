open import VSet.Prelude hiding (_∘_; id)
open import Cubical.Categories.Monoidal 
open import Cubical.Categories.Functor.Base 
open import Cubical.Categories.Constructions.BinProduct

module VSet.Cat.Trace {o ℓ} (M : MonoidalCategory o ℓ) where

open MonoidalCategory M renaming (C to 𝓒)

open import Level

open import Data.Product using (_,_)

open import Cubical.Categories.NaturalTransformation
   using (NatIso; NatTrans)
 
open import Cubical.Categories.Functor
   using (Functor; _∘F_; Id)

private
  variable
    A B C D X Y : ob
    f g : Hom[ A , B ]

record LeftTrace : Type (o ⊔ ℓ) where
  field
    -- Definition adapted from Agda Categories library. \cite{agda-categories}
    ltrace : ∀ {A B} → ∀ X → Hom[ X ⊗ A , X ⊗ B ] → Hom[ A , B ]

    lvanishing : ltrace unit (id ⊗ₕ f) ≡ f
    lvanishing₂
      : ∀ A B X Y → (f : Hom[ (Y ⊗ X) ⊗ A , (Y ⊗ X) ⊗ B ])
      → ltrace X (ltrace Y (α⁻¹⟨ Y , X , B ⟩ ∘ f ∘ α⟨ Y , X , A ⟩))
      ≡ ltrace (Y ⊗ X) f
    lsuperposing
      : ∀ A B Y → ∀ X (f : Hom[ X ⊗ A , X ⊗ B ])
      → ltrace X (α⁻¹⟨ X , B , Y ⟩ ∘ f ⊗ₕ id {Y} ∘ α⟨ X , A , Y ⟩)
      ≡ ltrace X f ⊗ₕ id {Y}
    lsliding
      : ∀ A B X → (f : Hom[ X ⊗ A , Y ⊗ B ]) → (g : Hom[ Y , X ])
      → ltrace X ((g ⊗ₕ id {B}) ∘ f) ≡ ltrace Y ( f ∘ (g ⊗ₕ id {A}))
    ltightening
      : ∀ A B C D X → (h : Hom[ A , B ]) (f : Hom[ X ⊗ B , X ⊗ C ]) (g : Hom[ C , D ])
      → ltrace X ((id {X} ⊗ₕ g) ∘ f ∘ (id {X} ⊗ₕ h)) ≡ g ∘ ltrace X f ∘ h
    lstrength
      : ∀ A B C D X → (f : Hom[ X ⊗ A , X ⊗ B ]) (g : Hom[ C , D ])
      → ltrace X (α⁻¹⟨ X , B , D ⟩ ∘ (f ⊗ₕ g) ∘ α⟨ X , A , C ⟩) ≡ ltrace X f ⊗ₕ g
