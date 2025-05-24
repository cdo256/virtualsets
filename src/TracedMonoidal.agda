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

record LeftTrace : Set (levelOfTerm M) where
  field
    braided : Braided

  open Braided braided public

  field
    ltrace : ∀ {X A B} → X ⊗₀ A ⇒ X ⊗₀ A → A ⇒ B

    vanishing₁  : ltrace {X = unit} (id ⊗₁ f) ≈ f
    vanishing₂  : ltrace {X = X} (ltrace {X = Y} (associator.from ∘ f ∘ associator.to))
                ≈ ltrace {X = Y ⊗₀ X} f
    superposing : ltrace {X = X} (associator.from ∘ f ⊗₁ id {Y} ∘ associator.to)
                ≈ ltrace {X = X} f ⊗₁ id {Y}
    yanking     : ltrace (braiding.⇒.η (X , X)) ≈ id

  
record RightTrace : Set (levelOfTerm M) where
  field
    braided : Braided

  open Braided braided public

  field
    rtrace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B

    vanishing₁  : rtrace {X = unit} (f ⊗₁ id) ≈ f
    vanishing₂  : rtrace {X = X} (rtrace {X = Y} (associator.to ∘ f ∘ associator.from))
                ≈ rtrace {X = X ⊗₀ Y} f
    superposing : rtrace {X = X} (associator.to ∘ id {Y} ⊗₁ f ∘ associator.from)
                ≈ id {Y} ⊗₁ rtrace {X = X} f
    yanking     : rtrace (braiding.⇐.η (X , X)) ≈ id

record PlanarTrace : Set (levelOfTerm M) where
  field
    braided : Braided
  
  
