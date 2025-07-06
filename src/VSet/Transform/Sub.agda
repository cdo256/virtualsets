module VSet.Transform.Sub where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
-- open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Fin hiding (pred)
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.Nat using (ℕ; zero; suc)
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Pred

sub : {X Y : SomeFin} (A : SomeFin) → (f : [ A + X ↣ A + Y ]) → [ X ↣ Y ]
sub zero f = f
sub (suc A) f  = sub A (pred f)
