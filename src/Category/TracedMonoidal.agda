open import Categories.Category
open import Categories.Category.Monoidal 
open import Categories.Category.Monoidal.Braided

module Category.TracedMonoidal {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} {Br : Braided M} where

open import Categories.Category.Monoidal.Traced

open Category C

open import Level

open import Data.Product using (_,_)

open import Categories.NaturalTransformation.NaturalIsomorphism
   using (NaturalIsomorphism)
 
open import Categories.Functor
   using (Functor; _∘F_) renaming (id to idF)


private
  variable
    A B X Y : Obj
    f g : A ⇒ B

-- See Joyal and Street 1991 Ch 4
record BalancedMonoidal : Set (levelOfTerm Br) where
  module braided = Braided Br
  open braided public
 
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

record BraidedLeftTrace : Set (levelOfTerm Br) where
  open Braided Br public

  field
    ltrace : ∀ {X A B} → X ⊗₀ A ⇒ X ⊗₀ B → A ⇒ B

    lvanishing₁  : ltrace {X = unit} (id ⊗₁ f) ≈ f
    lvanishing₂  : ltrace {X = X} (ltrace {X = Y} (associator.from ∘ f ∘ associator.to))
                 ≈ ltrace {X = Y ⊗₀ X} f
    lsuperposing : ltrace {X = X} (associator.from ∘ f ⊗₁ id {Y} ∘ associator.to)
                 ≈ ltrace {X = X} f ⊗₁ id {Y}
    lyanking     : ltrace (braiding.⇒.η (X , X)) ≈ id

  
record BraidedRightTrace : Set (levelOfTerm Br) where
  open Braided Br public

  field
    rtrace : ∀ {X A B} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B

    rvanishing₁  : rtrace {X = unit} (f ⊗₁ id) ≈ f
    rvanishing₂  : rtrace {X = X} (rtrace {X = Y} (associator.to ∘ f ∘ associator.from))
                 ≈ rtrace {X = X ⊗₀ Y} f
    rsuperposing : rtrace {X = X} (associator.to ∘ id {Y} ⊗₁ f ∘ associator.from)
                 ≈ id {Y} ⊗₁ rtrace {X = X} f
    ryanking     : rtrace (braiding.⇐.η (X , X)) ≈ id

record BraidedPlanarTrace : Set (levelOfTerm Br) where
  open Braided Br public

  field
    lt : BraidedLeftTrace
    rt : BraidedRightTrace 

record BraidedSphericalTrace : Set (levelOfTerm Br) where
  open Braided Br public

  field
    lt : BraidedLeftTrace
    rt : BraidedRightTrace

  open BraidedLeftTrace using (ltrace)
  open BraidedRightTrace using (rtrace)

  --- TODO
  -- field
  --   wrap : ∀ {X A B} → (f : X ⊗₀ A ⇒ X ⊗₀ B)
  --       → (ltrace lt) f ≈ (rtrace rt) (braiding.⇐.η ∘ f ∘ braiding.⇒.η)

