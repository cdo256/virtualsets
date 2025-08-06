module VSet.Transform.Compose.Base where

open import VSet.Prelude
open import Cubical.Data.Prod.Base hiding (map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import Cubical.Data.List.Base hiding ([_])
open import VSet.Data.Inj.Base
open import VSet.Transform.Elementary.Base 

_∘ʲ_ : ∀ {l m n} (g : Inj m n) (f : Inj l m) → Inj l n 
_∘ʲ_ g (nul _) = nul _
_∘ʲ_ {suc l} {suc m} {suc n} g (inc b f) =
  inc (apply g b) (remove b g ∘ʲ f)

_∘⁻ʲ_ : ∀ {l m n} (f : Inj l m) (g : Inj m n) → Inj l n 
f ∘⁻ʲ g = g ∘ʲ f
