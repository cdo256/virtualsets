module VSet.Transform.Trace.Tests where

open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inverse.Base 
open import VSet.Transform.Trace.Base 
open import VSet.Prelude

private
  variable
    l l' m m' n n' : ℕ



_ : remove f0 (inc f3 (nul 4)) ≡ (nul 4)
_ = refl

_ : remove f1 (inc f0 (inc f3 (nul 4))) ≡ (inc f0 (nul 4))
_ = refl

_ : remove f0 (cycle-l 5) ≡ idInj 5
_ = refl

_ : remove f1 (cycle-l 5) ≡ cycle-l 4
_ = refl

_ : remove f0 (insert f0 f1 (nul 4)) ≡ nul 4
_ = refl

_ : remove f1 (insert f1 f0 (inc f3 (nul 4))) ≡ inc f3 (nul 4)
_ = refl

_ : insert f0 f1 (remove f0 (inc f1 (nul 4))) ≡ inc f1 (nul 4)
_ = refl

_ : insert f1 f0 (remove f1 (inc f2 (inc f0 (nul 4)))) ≡ inc f2 (inc f0 (nul 4))
_ = refl

