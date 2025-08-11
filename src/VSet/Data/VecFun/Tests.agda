module VSet.Data.VecFun.Tests where

open import VSet.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec hiding (lookup)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.VecFun.Base
open import VSet.Data.VecFun.Properties
open import VSet.Data.Inj.Base
open import VSet.Transform.Inj.Elementary.Base

g : Inj 4 6 -- (3 2 4 0)
g = (inc f3 $ inc f2 $ inc f2 $ inc f0 $ nul 2)

_ = Inj→VecFun g ≡ (f3 ∷ f2 ∷ f4 ∷ f0 ∷ [])
_ = refl

_ = Inj→VecFun (idInj 3) ≡ (f0 ∷ f1 ∷ f2 ∷ [])
_ = refl

_ = Inj→VecFun (cycle-r 3) ≡ (f1 ∷ f2 ∷ f3 ∷ f0 ∷ [])
_ = refl

_ = Inj→VecFun (cycle-l 3) ≡ (f3 ∷ f0 ∷ f1 ∷ f2 ∷ [])
_ = refl

