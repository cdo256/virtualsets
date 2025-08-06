module VSet.Transform.Tensor.Identity where

open import VSet.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Data.Sum.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.List.Base hiding (elim; [_])
open import Cubical.Data.Maybe.Base hiding (elim)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inverse.Base
open import VSet.Transform.Tensor.Base
open import VSet.Transform.Tensor.Associator

private
  variable
    l l' m m' n n' : ℕ

module _ {l l' : ℕ} where
  η-p : Inj (0 + l) (0 + l') ≡ Inj l l'
  η-p = refl

  η-iso : Iso (Inj (0 + l) (0 + l')) (Inj l l')
  η-iso = pathToIso η-p

  η : Inj (0 + l) (0 + l') → Inj l l'
  η = transport η-p
