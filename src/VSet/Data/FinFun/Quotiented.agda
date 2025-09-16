module VSet.Data.FinFun.Quotiented where

open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.FinFun.Injection

open import Cubical.Foundations.Equiv.Base 
open import Cubical.HITs.PropositionalTruncation

record FinFunQ (n m : ℕ) : Type where
  constructor finFunQ
  field
    fun : ⟦ m ⟧ → ⟦ n ⟧
    inj : ∥ is-injective fun ∥₁

