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

_∘ʲ_ : ∀ {l m n} → (g : Inj m n) → (f : Inj l m) → Inj l n 
g ∘ʲ nul _ = nul _
inc c g ∘ʲ inc b f =
  let h'0 = apply (inc c g) (apply (inc b f) fzero)
  in inc h'0 (g ∘ʲ f)
