module VSet.VSet where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
-- open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
-- open import Cubical.Data.Nat.Properties
-- open import Cubical.Data.Empty renaming (elim to absurd)
-- open import Cubical.Data.Sum
-- open import Cubical.Data.Unit renaming (Unit to ⊤)
-- open import Cubical.Data.Fin.Base
-- open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Fin.Default
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Properties
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Pred
open import VSet.Transform.Tensor
open import VSet.Transform.Compose
open import VSet.Transform.Sub
open import VSet.Transform.Split

private
  variable
    A B X Y Z : SomeFin


-- -}
