open import Cubical.Foundations.Prelude

module Compat.1Lab.Data.Irr where

record Irr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor forget
  field
    .lower : A
