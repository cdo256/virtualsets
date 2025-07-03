module VSet.Function.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Core.Primitives

open import VSet.Path

private
  variable
    ℓ : Level

id : {A : Type} → A → A
id x = x
