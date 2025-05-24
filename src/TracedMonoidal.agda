open import Categories.Category
open import Categories.Category.Monoidal 

module TracedMonoidal {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} where

open import Categories.Category.Monoidal.Traced

open Category C

open import Level

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Braided M

private
  variable
    A B X Y : Obj
    f g : A ⇒ B

record RightTrace : Set (levelOfTerm M) where
  field
    braided : Braided

  open Braided braided public

  field
    trace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B

    vanishing₁  : trace {X = unit} (f ⊗₁ id) ≈ f
    vanishing₂  : trace {X = X} (trace {X = Y} (associator.to ∘ f ∘ associator.from))
                ≈ trace {X = X ⊗₀ Y} f
    superposing : trace {X = X} (associator.to ∘ id {Y} ⊗₁ f ∘ associator.from) ≈ id {Y} ⊗₁ trace {X = X} f
    yanking     : trace (braiding.⇒.η (X , X)) ≈ id
  

