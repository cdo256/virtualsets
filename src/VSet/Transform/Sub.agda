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
open import VSet.Data.Fin.Default
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Pred

infixl 8 _-ᶠ_

_-ᶠ_ : {A' X Y : SomeFin} → (f : [ A' + X ↣ A' + Y ])
    → (A : SomeFin) → {A ≡ A'}
    → [ X ↣ Y ]
_-ᶠ_ {zero} {X} {Y} f zero = f
_-ᶠ_ {zero} {X} {Y} f (suc A) {eq} = absurd (snotz eq)
_-ᶠ_ {suc A'} {X} {Y} f (zero) {eq} = absurd (znots eq)
_-ᶠ_ {suc A'} {X} {Y} f (suc A) = _-ᶠ_ (pred f) A

