module VSet.Transform.Elementary.Extra where

open import VSet.Prelude
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 

private
  variable
    l l' m m' n n' : ℕ

-- Untested.
remove-inv : (f : Inj (suc m) (suc n)) → (b : Fin (suc n)) → Maybe (Inj m n)
remove-inv {m = zero} (inc c f) b =
  decRec (λ _ → just f) (λ w → nothing) (b ≈?ᶠ c)
remove-inv {m = suc m} {n = suc n} (inc c f) b =
  decRec (λ _ → just f) step (b ≈?ᶠ c)
  where
    step : b ≉ᶠ c → Maybe (Inj (suc m) (suc n))
    step b≉c = map-Maybe (λ g → inc (fjoin b c (≉fsym b≉c)) g)
                         (remove-inv f (fjoin c b b≉c))

