module VSet.Data.SomeFin.Base where

open import VSet.Prelude

import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.Nat.Base
  using (ℕ)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

SomeFin : Type
SomeFin = ℕ

⟦_⟧ : (n : SomeFin) → Type
⟦ n ⟧ = Fin n

infixl 8 _+_

_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y


-- -}
