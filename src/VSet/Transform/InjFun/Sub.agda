module VSet.Transform.InjFun.Sub where

open import VSet.Prelude
open import Cubical.Data.Nat.Base
open import VSet.Data.Fin hiding (pred)

open import VSet.Data.InjFun.Injection
open import VSet.Transform.InjFun.Pred

trace : {X Y : ℕ} (A : ℕ) → (f : [ A + X ↣ A + Y ]) → [ X ↣ Y ]
trace zero f = f
trace (suc A) f = trace A (pred f)
