module VSet.Transform.Sub where

open import VSet.Prelude
open import VSet.Data.Fin hiding (pred)

open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Pred

sub : {X Y : SomeFin} (A : SomeFin) → (f : [ A + X ↣ A + Y ]) → [ X ↣ Y ]
sub zero f = f
sub (suc A) f = sub A (pred f)
