module VSet.Transform.Tensor.Associator where

open import VSet.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Data.Sum.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.List.Base hiding (elim; [_])
open import Cubical.Data.Maybe.Base hiding (elim)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inverse.Base
open import VSet.Transform.Tensor.Base

private
  variable
    l l' m m' n n' : ℕ

-- tensor : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
-- tensor (nul m') g = shift m' g
-- tensor {n' = n'} (inc b f) g = inc (finject n' b) (tensor f g)

shift1-tensor : (f : Inj m m') (g : Inj n n')
             → (shift1 f) ⊕ g ≡ shift1 (f ⊕ g)
shift1-tensor {m} {m'} {n} {n'} (nul m') g = refl
shift1-tensor {m} {m'} {n} {n'} (inc b f) g =
  shift1 (inc b f) ⊕ g ≡⟨ refl ⟩
  inc (fsuc b) (shift1 f) ⊕ g
    ≡⟨ refl ⟩
  inc (finject n' (fsuc b)) (shift1 f ⊕ g)
    ≡⟨ cong₂ inc (finject-fsuc-reorder b) (shift1-tensor f g) ⟩
  inc (fsuc (finject n' b)) (shift1 (f ⊕ g))
    ≡⟨ refl ⟩
  shift1 (inc (finject n' b) (f ⊕ g))
    ≡⟨ refl ⟩
  shift1 (inc b f ⊕ g) ▯

-- subst2-shift1-reorder
--   : subst2 Inj refl (+-assoc (suc l') m' n') (shift (suc l') (f ⊕ g))
--   ≡ shift1 (subst2 Inj refl (+-assoc l' m' n') (shift l' (f ⊕ g)))

-- subst-fsuc-reorder
--   : ∀ {m m' n n' : ℕ} → (p : m ≡ m') (q : n ≡ n') (a : Fin x)
--   → transport (λ i → Fin (suc (p i))) (fsuc a)
--   ≡ shift1 (subst2 Inj p q a)
-- subst-fsuc-reorder p a = transport-reorder Fin suc fsuc p a


shift-tensor : (l' : ℕ) (f : Inj m m') (g : Inj n n')
             → (shift l' f) ⊕ g ≡ subst2 Inj refl (+-assoc l' m' n') (shift l' (f ⊕ g))
shift-tensor {m} {m'} {n} {n'} zero f g =
  shift zero f ⊕ g ≡⟨ sym (transportRefl (shift zero f ⊕ g)) ⟩
  transport refl (shift zero (f ⊕ g)) ≡⟨ refl ⟩
  subst2 Inj refl (+-assoc zero m' n') (shift zero (f ⊕ g)) ▯
shift-tensor {m} {m'} {n} {n'} (suc l') f g =
  (shift (suc l') f) ⊕ g
    ≡⟨ refl ⟩
  (shift1 (shift l' f)) ⊕ g
    ≡⟨ shift1-tensor (shift l' f) g ⟩
  shift1 ((shift l' f) ⊕ g)
    ≡⟨ cong shift1 (shift-tensor l' f g) ⟩
  shift1 (subst2 Inj refl (+-assoc l' m' n') (shift l' (f ⊕ g)))
    ≡⟨ sym (subst2-reorder Inj id suc shift1 refl
                           (+-assoc l' m' n') (shift l' (f ⊕ g))) ⟩
  subst2 Inj refl (+-assoc (suc l') m' n') (shift (suc l') (f ⊕ g)) ▯

α : {l l' m m' n n' : ℕ} (f : Inj l l') (g : Inj m m') (h : Inj n n')
  → ((f ⊕ g) ⊕ h) ≡ subst2 Inj (+-assoc l m n) (+-assoc l' m' n') (f ⊕ (g ⊕ h))
α {zero} {l'} {m} {m'} {n} {n'} (nul _) g h =
  ((nul l' ⊕ g) ⊕ h)
    ≡⟨ refl ⟩
  ((shift l' g) ⊕ h)
    ≡⟨ {!!} ⟩
  ((nul l' ⊕ g) ⊕ h)
    ≡⟨ {!!} ⟩
  subst2 Inj (+-assoc zero m n) (+-assoc l' m' n') (nul l' ⊕ (g ⊕ h)) ▯
α {suc l} f g h = {!!}
