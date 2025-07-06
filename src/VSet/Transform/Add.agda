module VSet.Transform.Add where

open import VSet.Prelude
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.Nat using (ℕ; zero; suc)
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Data.SomeFin.Properties
open import VSet.Transform.Pred

add : ∀ {X Y : SomeFin} → (A : SomeFin) → (g : [ X ↣ Y ]) → [ A + X ↣ A + Y ]
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
    inj (fsuc x) (fsuc y) shx≡shy = cong fsuc (h-inj x y (fsuc-injective shx≡shy))
