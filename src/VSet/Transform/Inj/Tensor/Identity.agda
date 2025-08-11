module VSet.Transform.Inj.Tensor.Identity where

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
open import VSet.Transform.Inj.Inverse.Base
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Associator

private
  variable
    l l' m m' n n' : ℕ

module _ {l l' : ℕ} where
  η-p : Inj (l + 0) (l' + 0) ≡ Inj l l'
  η-p = cong₂ Inj (+-zero l) (+-zero l')

  η-iso : Iso (Inj (l + 0) (l' + 0)) (Inj l l')
  η-iso = pathToIso η-p

  η : Inj (l + 0) (l' + 0) → Inj l l'
  η = transport η-p
