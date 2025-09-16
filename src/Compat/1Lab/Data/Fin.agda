module Compat.1Lab.Data.Fin where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Nat.Order
open import Compat.1Lab.Data.Irr

record Fin (n : Nat) : Type where
  constructor fin
  field
    lower       : Nat
    ⦃ bounded ⦄ : Irr (lower < n)

open Fin
