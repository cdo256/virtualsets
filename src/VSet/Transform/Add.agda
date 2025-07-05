module VSet.Transform.Add where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Core.Primitives
-- open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.SumFin.Base
open import Cubical.Data.SumFin.Properties

open import VSet.Path
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Data.SomeFin.Properties
open import VSet.Transform.Pred

add : ∀ {X Y : SomeFin} → (A : SomeFin) → (g : Fin X ↣ Fin Y) → [ A + X ↣ A + Y ]
add {X} {Y} zero g = g
add {X} {Y} (suc A) g = f , inj
  where
    h = fst $ add A g
    h-inj = snd $ add A g
    f : ⟦ suc (A + X) ⟧ → ⟦ suc (A + Y) ⟧
    f fzero = fzero
    f (fsuc x) = fsuc (h x)
    inj : is-injective f
    inj fzero fzero f0≡f0 = refl
    inj fzero (fsuc y) f0≡fy' = absurd (fzero≢fsuc (h y) f0≡fy')
    inj (fsuc x) fzero fx'≡f0 = absurd (fsuc≢fzero (h x) fx'≡f0) 
    inj (fsuc x) (fsuc y) fx≡fy = cong fsuc (h-inj x y {!!})
