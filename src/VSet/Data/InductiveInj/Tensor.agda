module VSet.Data.InductiveInj.Tensor where

open import VSet.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Data.Sum.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.List.Base hiding (elim; [_])
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.InductiveInj.Base 
open import VSet.Data.InductiveInj.Order 
open import VSet.Data.InductiveInj.Inverse 
open import Cubical.Data.Maybe.Base hiding (elim)
open import VSet.Data.InductiveInj.Properties

private
  variable
    l l' m m' n n' : ℕ


shift1 : ∀ {m n} → (f : Inj m n) → Inj m (suc n)
shift1 (nul _) = nul _
shift1 (inc b f) =
  inc (fsuc b) (shift1 f)

shift : ∀ {m n} → (l : ℕ) → (f : Inj m n) → Inj m (l + n)
shift zero f = f
shift (suc l) f = shift1 (shift l f) 

tensor : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
tensor (nul m') g =
  shift m' g
tensor (inc b f) (nul n') =
  inc (finject n' b) (tensor f (nul n'))
tensor (inc b f) (inc b' g) =
  inc (finject (suc _) b) (tensor f (inc b' g))

_⊕_ : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
f ⊕ g = tensor f g
