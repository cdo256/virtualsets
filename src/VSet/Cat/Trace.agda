open import VSet.Prelude hiding (_∘_; id)
open import Cubical.Categories.Monoidal 
open import Cubical.Categories.Functor.Base 
open import Cubical.Categories.Constructions.BinProduct

module VSet.Cat.Trace {o ℓ} {M : MonoidalCategory o ℓ} where

open MonoidalCategory M

open import Level

open import Data.Product using (_,_)

open import Cubical.Categories.NaturalTransformation
   using (NatIso; NatTrans)
 
open import Cubical.Categories.Functor
   using (Functor; _∘F_; Id)

private
  variable
    A B X Y : ob
    f g : Hom[ A , B ]

record LeftTrace : Type _ where

  field
    -- Definition adapted from Agda Categories library. \cite{agda-categories}
    ltrace : ∀ {X A B} → Hom[ X ⊗ A , X ⊗ B ] → Hom[ A , B ]

    lvanishing  : ltrace {X = unit} (id ⊗ₕ f) ≡ f
    lvanishing₂
      : {f : Hom[ (Y ⊗ X) ⊗ A , (Y ⊗ X) ⊗ B ]}
      → ltrace {X = X} (ltrace {X = Y} (α⁻¹⟨ Y , X , B ⟩ ∘ f ∘ α⟨ Y , X , A ⟩))
      ≡ ltrace {X = Y ⊗ X} f
    lsuperposing
      : {f : Hom[ X ⊗ A , X ⊗ B ]}
      → ltrace {X = X} (α⁻¹⟨ X , B , Y ⟩ ∘ f ⊗ₕ id {Y} ∘ α⟨ X , A , Y ⟩)
      ≡ ltrace {X = X} f ⊗ₕ id {Y}
