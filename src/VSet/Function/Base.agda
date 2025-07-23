-- Based on stdlib src/Funciton/Base.agda
module VSet.Function.Base where

open import VSet.Prelude
open import Function.Base public

private
  variable
    a b c d : Level
    A : Type a
    B : Type b
    C : Type c
    D : Type d

infixr 1 _-⊎-_
infixr 2 _-×-_ _-,-_

_-⊎-_ : (A → B → Type c) → (A → B → Type d) → (A → B → Type _)
f -⊎- g = f -⟪ _⊎_ ⟫- g

_-×-_ : (A → B → Type c) → (A → B → Type d) → (A → B → Type _)
f -×- g = f -⟪ _×_ ⟫- g

_-,-_ : (A → B → C) → (A → B → D) → (A → B → C × D)
f -,- g = f -⟪ _,_ ⟫- g
