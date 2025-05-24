open import Categories.Category
open import Categories.Category.Monoidal 

module TracedMonoidal {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} where

open import Categories.Category.Monoidal.Traced

open Category C

open import Level

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Braided M

open import Categories.NaturalTransformation.NaturalIsomorphism
   using (NaturalIsomorphism)
 
open import Categories.Functor
   using (Functor; _∘F_) renaming (id to idF)


private
  variable
    A B X Y : Obj
    f g : A ⇒ B

-- See Joyal and Street 1991 Ch 4
record BalancedMonoidal : Set (levelOfTerm M) where
  field
    braided : Braided

  module braided = Braided braided
  open braided public
    -- using (_⊗₀_; _⊗₁_) renaming (B to c)
 
  field
    twist : NaturalIsomorphism (idF {C = C}) (idF {C = C}) 

  module twist = NaturalIsomorphism twist

  private
    θ : ∀ {A} → A ⇒ A
    θ {A} = twist.⇒.η A
    c : ∀ {X Y} → (X ⊗₀ Y) ⇒ (Y ⊗₀ X)
    c {X} {Y} = braiding.⇒.η (X , Y)

  field 
    twistComposition :
        θ {A ⊗₀ B}
      ≈ c {B} {A} ∘ θ {B} ⊗₁ θ {A} ∘ c {A} {B}
    twistIdentity : θ {A} ≈ Category.id C {A}



-- record RightTrace : Set (levelOfTerm M) where
--   field
--     braided : Braided
-- 
--   open Braided braided public
-- 
--   field
--     trace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
-- 
--     vanishing₁  : trace {X = unit} (f ⊗₁ id) ≈ f
--     vanishing₂  : trace {X = X} (trace {X = Y} (associator.to ∘ f ∘ associator.from))
--                 ≈ trace {X = X ⊗₀ Y} f
--     superposing : trace {X = X} (associator.to ∘ id {Y} ⊗₁ f ∘ associator.from) ≈ id {Y} ⊗₁ trace {X = X} f
--     yanking     : trace (braiding.⇒.η (X , X)) ≈ id
  

