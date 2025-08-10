module VSet.Transform.Tensor.Properties where

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
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Elementary.Base
open import VSet.Transform.Inverse.Base
open import VSet.Transform.Compose.Base
open import VSet.Transform.Tensor.Base
open import Cubical.Data.Maybe.Base hiding (elim)

private
  variable
    l l' l'' m m' m'' n n' n'' : ℕ

shift≡shift' : ∀ {m n} → (l : ℕ) → (f : Inj m n) → shift l f ≡ shift' l f
shift≡shift' {m} {n} zero (nul .n) = refl
shift≡shift' {m} {n} (suc l) (nul .n) =
  shift (suc l) (nul n) ≡⟨ refl ⟩
  shift1 (shift l (nul n)) ≡⟨ cong shift1 (shift≡shift' l (nul n)) ⟩
  shift1 (nul (l + n)) ≡⟨ refl ⟩
  nul (suc l + n) ≡⟨ refl ⟩
  shift' (suc l) (nul n) ▯
shift≡shift' {suc m} {suc n} zero (inc b f) =
  shift zero (inc b f)
    ≡⟨ refl ⟩
  inc b f
    ≡⟨ refl ⟩
  inc b (shift zero f)
    ≡⟨ cong₂ inc (sym (transportRefl b)) (shift≡shift' zero f) ⟩
  inc (subst Fin refl b) (shift' zero f)
    ≡⟨ sym (transportRefl _) ⟩
  subst2 Inj refl refl (inc (subst Fin refl (fshift zero b)) (shift' zero f))
    ≡⟨ refl ⟩
  shift' zero (inc b f) ▯
shift≡shift' {suc m} {suc n} (suc l) (inc b f) =
  shift (suc l) (inc b f)
    ≡⟨ refl ⟩
  shift1 (shift l (inc b f))
    ≡⟨ cong shift1 (shift≡shift' l (inc b f)) ⟩
  shift1 (shift' l (inc b f))
    ≡⟨ refl ⟩
  shift1 (subst2 Inj refl (sym p) (inc (subst Fin p (fshift l b)) (shift' l f)))
    ≡⟨ sym (subst2-reorder Inj id suc shift1 refl (sym p) (inc (subst Fin p (fshift l b)) (shift' l f))) ⟩
  subst2 Inj refl (sym q) 
         (shift1 (inc (subst Fin p (fshift l b)) (shift' l f)))
    ≡⟨ refl ⟩
  subst2 Inj refl (sym q) 
         (inc (fsuc (subst Fin p (fshift l b))) (shift1 (shift' l f)))
    ≡⟨ cong (subst2 Inj refl (sym q))
            (cong₂ inc (sym (subst-fsuc-reorder p (fshift l b)))
                       (cong shift1 (sym (shift≡shift' l f)))) ⟩
  subst2 Inj refl (sym q) 
         (inc (subst Fin q (fsuc (fshift l b)))
              (shift (suc l) f))
    ≡⟨ cong (subst2 Inj refl (sym q))
             (cong (inc (subst Fin q (fshift (suc l) b)))
                   (shift≡shift' (suc l) f)) ⟩
  subst2 Inj refl (sym q)
         (inc (subst Fin q (fshift (suc l) b))
              (shift' (suc l) f))
    ≡⟨ refl ⟩
  shift' (suc l) (inc b f) ▯
  where
    p = +-suc l n
    q = +-suc (suc l) n 

𝟙⊕𝟙≡𝟙 : 𝟙 {m} ⊕ 𝟙 {n} ≡ 𝟙 {m + n}
𝟙⊕𝟙≡𝟙 {zero} {n} = refl
𝟙⊕𝟙≡𝟙 {suc m} {n} = cong (inc f0) (𝟙⊕𝟙≡𝟙 {m} {n})

nul-⊕-nul : {m n : ℕ} → nul m ⊕ nul n ≡ nul (m + n)
nul-⊕-nul {zero} = refl
nul-⊕-nul {suc m} {n} =
  shift (suc m) (nul n) ≡⟨ refl ⟩
  shift1 (shift m (nul n)) ≡⟨ cong shift1 (nul-⊕-nul {m} {n}) ⟩
  nul (suc m + n) ▯

∘ʲ-nul : {m n : ℕ} → (f : Inj m n) → f ∘ʲ nul m ≡ nul n
∘ʲ-nul f = refl

⊕-preserves-∘ : ∀ {m m' m'' n n' n''}
              → (f : Inj m m') (f' : Inj m' m'') (g : Inj n n') (g' : Inj n' n'')
              → (f' ∘ʲ f) ⊕ (g' ∘ʲ g) ≡ (f' ⊕ g') ∘ʲ (f ⊕ g)
⊕-preserves-∘ {zero} {m'} {m''} {zero} {n'} {n''} (nul m') f' (nul n') g' =
  (f' ∘ʲ nul m') ⊕ (g' ∘ʲ nul n')
    ≡⟨ refl ⟩
  (nul m'') ⊕ (nul n'')
    ≡⟨ nul-⊕-nul {m''} ⟩
  nul (m'' + n'')
    ≡⟨ refl ⟩
  (f' ⊕ g') ∘ʲ nul (m' + n')
    ≡⟨ cong (tensor f' g' ∘ʲ_) (sym (nul-⊕-nul {m'})) ⟩
  (f' ⊕ g') ∘ʲ (nul m' ⊕ nul n') ▯
⊕-preserves-∘ {zero} {m'} {m''} {suc n} {suc n'} {suc n''} (nul m') f' (inc b g) g' =
  (f' ∘ʲ nul m') ⊕ (g' ∘ʲ inc b g)
    ≡⟨ refl ⟩
  nul m'' ⊕ inc (apply g' b) (remove b g' ∘ʲ g)
    ≡⟨ refl ⟩
  shift m'' (inc (apply g' b) (remove b g' ∘ʲ g))
    ≡⟨ shift≡shift' m'' (inc (apply g' b) (remove b g' ∘ʲ g)) ⟩
  shift' m'' (inc (apply g' b) (remove b g' ∘ʲ g))
    ≡⟨ refl ⟩
  subst2 Inj refl (sym q)
         (inc (subst Fin q (fshift m'' (apply g' b)))
              (shift' m'' (remove b g' ∘ʲ g)))
    ≡⟨ cong (subst2 Inj refl (sym q)) refl ⟩
  subst2 Inj refl (sym q)
         (inc (subst Fin q {!!}) {!!})
    ≡⟨ {!!} ⟩
  subst2 Inj refl (sym q)
         (subst2 Inj p q (f' ⊕ g')
         ∘ʲ inc (subst Fin p (fshift m' b)) (shift' m' g))
    ≡⟨ {!!} ⟩
  (f' ⊕ g') ∘ʲ subst2 Inj refl (sym p) (inc (subst Fin p (fshift m' b)) (shift' m' g))
    ≡⟨ cong ((f' ⊕ g') ∘ʲ_) (sym (shift≡shift' m' (inc b g))) ⟩
  (f' ⊕ g') ∘ʲ shift m' (inc b g)
    ≡⟨ refl ⟩
  (f' ⊕ g') ∘ʲ (nul m' ⊕ inc b g) ▯
  where
    p = +-suc m' n'
    q = +-suc m'' n''
⊕-preserves-∘ {suc m} {suc m'} {m''} {zero} {n'} {n''} (inc b f) f' (nul .n') g' = {!!}
⊕-preserves-∘ {m} {m'} {m''} {n} {n'} {n''} (inc b f) f' (inc b₁ g) g' = {!!}

