module VSet.Transform.FinFun.Sub where

open import VSet.Prelude
open import Cubical.Data.Nat.Base
open import VSet.Data.Fin hiding (pred)

open import VSet.Data.FinFun.Injection
open import VSet.Transform.FinFun.Pred

sub : {X Y : ℕ} (A : ℕ) → (f : [ A + X ↣ A + Y ]) → [ X ↣ Y ]
sub zero f = f
sub (suc A) f = sub A (pred f)
