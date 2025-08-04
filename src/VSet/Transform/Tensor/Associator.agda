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
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inverse.Base
open import VSet.Transform.Tensor.Base

private
  variable
    l l' m m' n n' : ℕ

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
  (nul l' ⊕ g) ⊕ h
    ≡⟨ refl ⟩
  (shift l' g) ⊕ h
    ≡⟨ shift-tensor l' g h ⟩
  subst2 Inj refl (+-assoc l' m' n') (shift l' (g ⊕ h))
    ≡⟨ refl ⟩
  subst2 Inj (+-assoc zero m n) (+-assoc l' m' n') (nul l' ⊕ (g ⊕ h)) ▯
α {suc l} {suc l'} {m} {m'} {n} {n'} (inc b f) g h =
  (inc b f ⊕ g) ⊕ h
    ≡⟨ refl ⟩
  (inc (finject m' b) (f ⊕ g)) ⊕ h
    ≡⟨ refl ⟩
  inc (finject n' (finject m' b)) ((f ⊕ g) ⊕ h)
    ≡⟨ cong (λ ○ → inc ○ ((f ⊕ g) ⊕ h)) (finject-+ (suc l') m' n' b)  ⟩
  inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b)) ((f ⊕ g) ⊕ h)
    ≡⟨ cong (inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b)))
            (α f g h) ⟩
  inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b))
      (subst2 Inj (+-assoc l m n) (+-assoc l' m' n') (f ⊕ (g ⊕ h)))
    ≡⟨ subst2-inc-reorder (+-assoc l m n) (+-assoc l' m' n')
                          (finject (m' + n') b) (f ⊕ (g ⊕ h)) ⟩
  subst2 Injsuc (+-assoc l m n) (+-assoc l' m' n')
         (inc (finject (m' + n') b) (f ⊕ (g ⊕ h)))
    ≡⟨ refl ⟩
  subst2 Inj (+-assoc (suc l) m n) (+-assoc (suc l') m' n')
         (inc b f ⊕ (g ⊕ h)) ▯
