module VSet.Transform.Inj.Tensor.Associator where

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
open import VSet.Transform.Inj.Inverse.Base
open import VSet.Transform.Inj.Tensor.Base

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

shift-tensor-cast
  : (l' : ℕ) (f : Inj m m') (g : Inj n n')
  → (shift l' f) ⊕ g ≡ jcast refl (+-assoc l' m' n') (shift l' (f ⊕ g))
shift-tensor-cast {m} {m'} {n} {n'} zero f g = 
  shift zero f ⊕ g ≡⟨ refl ⟩
  shift zero (f ⊕ g) ≡⟨ sym (jcast-loop _ _ _) ⟩
  jcast refl (+-assoc zero m' n') (shift zero (f ⊕ g)) ▯
shift-tensor-cast {m} {m'} {n} {n'} (suc l') f g =
  (shift (suc l') f) ⊕ g
    ≡⟨ refl ⟩
  (shift1 (shift l' f)) ⊕ g
    ≡⟨ shift1-tensor (shift l' f) g ⟩
  shift1 ((shift l' f) ⊕ g)
    ≡⟨ cong shift1 (shift-tensor-cast l' f g) ⟩
  shift1 (jcast refl (+-assoc l' m' n') (shift l' (f ⊕ g)))
    ≡⟨ {!!} ⟩
  jcast refl (cong suc (+-assoc l' m' n')) (shift1 (shift l' (f ⊕ g)))
    ≡⟨ refl ⟩
  jcast refl (+-assoc (suc l') m' n') (shift (suc l') (f ⊕ g)) ▯

-- jcast-reorder
--   : ∀ {m m' n n' : ℕ}
--   → (ϕ : ℕ → ℕ) (ψ : ℕ → ℕ) (ρ : {x y : ℕ} → Inj x y → Inj (ϕ x) (ψ y))
--   → (p : m ≡ m') (q : n ≡ n') (f : Inj m n)
--   → jcast (cong ϕ p) (cong ψ q) (ρ f)
--   ≡ ρ (jcast p q f)
-- jcast-reorder {zero} {zero} {n} {n'} ϕ ψ ρ p q (nul _) = {!!}
-- jcast-reorder {zero} {suc m'} {n} {n'} ϕ ψ ρ p q (nul _) = {!!}
-- jcast-reorder {suc m} {m'} {n} {n'} ϕ ψ ρ p q (inc b f) = {!!}

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


module _ {l l' m m' n n' : ℕ} where
  α-p-dom : l + (m + n) ≡ (l + m) + n
  α-p-dom = +-assoc l m n

  α-p-cod : l' + (m' + n') ≡ (l' + m') + n'
  α-p-cod = +-assoc l' m' n'

  α-p : Inj (l + (m + n)) (l' + (m' + n'))
      ≡ Inj ((l + m) + n) ((l' + m') + n')
  α-p =
    cong₂ Inj (+-assoc l m n) (+-assoc l' m' n')

  α-iso : Iso (Inj (l + (m + n)) (l' + (m' + n')))
              (Inj ((l + m) + n) ((l' + m') + n'))
  α-iso = pathToIso α-p

  α : Inj (l + (m + n)) (l' + (m' + n')) → Inj ((l + m) + n) ((l' + m') + n')
  α = Iso.fun α-iso 

  α⁻¹ : Inj ((l + m) + n) ((l' + m') + n') → Inj (l + (m + n)) (l' + (m' + n')) 
  α⁻¹ = Iso.inv α-iso 

assoc : {l l' m m' n n' : ℕ} → (f : Inj l l') (g : Inj m m') (h : Inj n n')
  → ((f ⊕ g) ⊕ h) ≡ transport (α-p {l} {l'}) (f ⊕ (g ⊕ h))
assoc {zero} {l'} {m} {m'} {n} {n'} (nul _) g h =
  (nul l' ⊕ g) ⊕ h
    ≡⟨ refl ⟩
  (shift l' g) ⊕ h
    ≡⟨ shift-tensor l' g h ⟩
  subst2 Inj refl (+-assoc l' m' n') (shift l' (g ⊕ h))
    ≡⟨ refl ⟩
  subst2 Inj (+-assoc zero m n) (+-assoc l' m' n') (nul l' ⊕ (g ⊕ h)) ▯
assoc {suc l} {suc l'} {m} {m'} {n} {n'} (inc b f) g h =
  (inc b f ⊕ g) ⊕ h
    ≡⟨ refl ⟩
  (inc (finject m' b) (f ⊕ g)) ⊕ h
    ≡⟨ refl ⟩
  inc (finject n' (finject m' b)) ((f ⊕ g) ⊕ h)
    ≡⟨ cong (λ ○ → inc ○ ((f ⊕ g) ⊕ h)) (finject-+ (suc l') m' n' b)  ⟩
  inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b)) ((f ⊕ g) ⊕ h)
    ≡⟨ cong (inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b)))
            (assoc f g h) ⟩
  inc (subst (Fin ∘ suc) (+-assoc l' m' n') (finject (m' + n') b))
      (subst2 Inj (+-assoc l m n) (+-assoc l' m' n') (f ⊕ (g ⊕ h)))
    ≡⟨ sym (subst2-inc-reorder (+-assoc l m n) (+-assoc l' m' n')
                               (finject (m' + n') b) (f ⊕ (g ⊕ h))) ⟩
  subst2 Injsuc (+-assoc l m n) (+-assoc l' m' n')
        (inc (finject (m' + n') b) (f ⊕ (g ⊕ h)))
    ≡⟨ refl ⟩
  subst2 Inj (+-assoc (suc l) m n) (+-assoc (suc l') m' n')
        (inc b f ⊕ (g ⊕ h)) ▯

unassoc : (f : Inj l l') (g : Inj m m') (h : Inj n n')
  → (f ⊕ (g ⊕ h)) ≡ (α⁻¹ {l} {l'}) ((f ⊕ g) ⊕ h)
unassoc {l} {l'} {m} {m'} {n} {n'} f g h =
  let α-p = α-p {l} {l'} {m} {m'} {n} {n'}  
  in
  (f ⊕ (g ⊕ h))
    ≡⟨ sym (transport⁻Transport α-p (f ⊕ (g ⊕ h))) ⟩
  transport (sym α-p )
    (transport α-p (f ⊕ (g ⊕ h))) 
    ≡⟨ sym (cong (transport (sym α-p)) (assoc f g h)) ⟩
  transport (sym α-p) ((f ⊕ g) ⊕ h) ▯

module _ {m m' : ℕ} where
  ρ-p-dom : m + 0 ≡ m
  ρ-p-dom = +-zero m

  ρ-p-cod : m' + 0 ≡ m'
  ρ-p-cod = +-zero m'

  ρ-p : Inj (m + 0) (m' + 0) ≡ Inj m m'
  ρ-p =
    cong₂ Inj ρ-p-dom ρ-p-cod

  ρ-iso : Iso (Inj (m + 0) (m' + 0))
              (Inj m m')
  ρ-iso = pathToIso ρ-p

  ρ : Inj (m + 0) (m' + 0) → Inj m m'
  ρ = Iso.fun ρ-iso 

  ρ⁻¹ : Inj m m' → Inj (m + 0) (m' + 0)
  ρ⁻¹ = Iso.inv ρ-iso 

right-unit : {m m' : ℕ} → (f : Inj m m')
           → f ≡ transport ρ-p (f ⊕ 𝟘)
right-unit (nul m') =
  nul m'
    ≡⟨ nul≡subst-nul (+-zero m') ⟩
  transport ρ-p (nul (m' + 0))
    ≡⟨ cong (transport ρ-p) refl ⟩
  transport ρ-p (nul m' ⊕ 𝟘) ▯
right-unit {suc m} {suc m'} (inc fzero f) =
  inc fzero f
    ≡⟨ cong₂ inc (fzero≡subst-fzero (+-zero m'))
                 (right-unit f) ⟩
  inc (subst (Fin ∘ suc) (+-zero m') fzero)
      (subst2 Inj (+-zero m) (+-zero m') (f ⊕ 𝟘))
    ≡⟨ sym (subst2-inc-reorder (+-zero m) (+-zero m') fzero (f ⊕ 𝟘)) ⟩
  transport ρ-p (inc fzero (f ⊕ 𝟘))
    ≡⟨ refl ⟩
  transport ρ-p (inc (finject 0 fzero) (f ⊕ 𝟘))
    ≡⟨ refl ⟩
  transport ρ-p (inc fzero f ⊕ 𝟘) ▯
right-unit {suc m} {suc m'} (inc (fsuc b) f) =
  inc (fsuc b) f
    ≡⟨ cong (λ ○ → inc (fsuc ○) f) (sym (substSubst⁻ Fin (+-zero m') b)) ⟩
  inc (fsuc (subst Fin (+-zero m') (subst Fin (sym (+-zero m')) b))) f
    ≡⟨ cong (λ ○ → inc (fsuc (subst Fin (+-zero m') ○)) f) (sym (finject0≡subst b)) ⟩
  inc (fsuc (subst Fin (+-zero m') (finject 0 b))) f
    ≡⟨ cong₂ inc (sym (subst-fsuc-reorder (+-zero m') (finject 0 b)))
                 (right-unit f) ⟩
  inc (subst (Fin ∘ suc) (+-zero m') (fsuc (finject 0 b)))
      (subst2 Inj (+-zero m) (+-zero m') (f ⊕ 𝟘))
    ≡⟨ sym (subst2-inc-reorder (+-zero m) (+-zero m') (fsuc (finject 0 b)) (f ⊕ 𝟘)) ⟩
  transport ρ-p (inc (fsuc (finject 0 b)) (f ⊕ 𝟘))
    ≡⟨ refl ⟩
  transport ρ-p (inc (finject 0 (fsuc b)) (f ⊕ 𝟘))
    ≡⟨ refl ⟩
  transport ρ-p (inc (fsuc b) f ⊕ 𝟘) ▯

module _ {m m' : ℕ} where
  η-p-dom : 0 + m ≡ m
  η-p-dom = refl

  η-p-cod : 0 + m' ≡ m'
  η-p-cod = refl

  η-p : Inj (0 + m) (0 + m') ≡ Inj m m'
  η-p =
    cong₂ Inj η-p-dom η-p-cod

  η-iso : Iso (Inj (0 + m) (0 + m'))
              (Inj m m')
  η-iso = pathToIso η-p

  η : Inj (0 + m) (0 + m') → Inj m m'
  η = Iso.fun η-iso 

  η⁻¹ : Inj m m' → Inj (0 + m) (0 + m')
  η⁻¹ = Iso.inv η-iso 

left-unit : {m m' : ℕ} → (f : Inj m m')
          → f ≡ transport η-p (𝟘 ⊕ f)
left-unit f = sym (transportRefl f)

