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

-- w : ?
-- g'  : Inj (suc n') (suc n'')
-- g   : Inj n n'
-- b   : Fin (suc n')
-- f'  : Inj m' m''
-- n'' : ℕ
-- n'  : ℕ
-- n   : ℕ
-- m'' : ℕ
-- m'  : ℕ
-- subst2 Inj refl (sym q)
--         (subst2 Inj p q g
--         ∘ʲ inc (subst Fin p (fshift m' b)) (shift' m' g))
--   ≡⟨ {!!} ⟩
-- (f' ⊕ g') ∘ʲ subst2 Inj refl (sym p) (inc (subst Fin p (fshift m' b)) (shift' m' g))

w : {l m n : ℕ} → (b : Fin (suc n))
  → (g : Inj m n)
  → inc (subst Fin (+-suc l n) (fshift l b)) (shift' l g)
  ≡ {!!}
w {zero} {m} {n} b g = {!!}
w {suc l} {m} {n} b g = {!!}

apply-shift1 : {m n : ℕ} (f : Inj m n) (a : Fin m)
             → apply (shift1 f) a ≡ fsuc (apply f a)
apply-shift1 {suc m} {suc n} (inc b f) fzero = refl
apply-shift1 {suc m} {suc n} (inc b f) (fsuc a) =
  apply (shift1 (inc b f)) (fsuc a)
    ≡⟨ refl ⟩
  apply (inc (fsuc b) (shift1 f)) (fsuc a)
    ≡⟨ refl ⟩
  fsplice (fsuc b) (apply (shift1 f) a)
    ≡⟨ cong (fsplice (fsuc b)) (apply-shift1 f a) ⟩
  fsplice (fsuc b) (fsuc (apply f a))
    ≡⟨ refl ⟩
  fsuc (fsplice b (apply f a))
    ≡⟨ refl ⟩
  fsuc (apply (inc b f) (fsuc a)) ▯

apply-shift : (l : ℕ) {m n : ℕ} (f : Inj m n) (a : Fin m)
            → apply (shift l f) a ≡ fshift l (apply f a)
apply-shift zero {suc m} {suc n} f a = refl
apply-shift (suc l) {suc m} {suc n} (inc b f) a =
  apply (shift (suc l) (inc b f)) a 
    ≡⟨ refl ⟩
  apply (shift1 (shift l (inc b f))) a 
    ≡⟨ apply-shift1 (shift l (inc b f)) a ⟩
  fsuc (apply (shift l (inc b f)) a)
    ≡⟨ cong fsuc (apply-shift l (inc b f) a) ⟩
  fsuc (fshift l (apply (inc b f) a))
    ≡⟨ refl ⟩
  fshift (suc l) (apply (inc b f) a) ▯

shift1-remove
  : {l m n : ℕ} (f : Inj l m) (g : Inj m n) (b : Fin (suc m)) (c : Fin (suc n))
  → shift1 (remove b (inc c g) ∘ʲ f)
  ≡ remove b (inc (fsuc c) (shift1 g)) ∘ʲ f
shift1-remove {l} {m} {n} f g b c = {!!}

∘ʲ-preserves-shift1
  : {l m n : ℕ} → (g : Inj m n) (f : Inj l m)
  → (shift1 (g ∘ʲ f))
  ≡ (shift1 g) ∘ʲ f
∘ʲ-preserves-shift1 {zero} {m} {n} g (nul m) =
  shift1 (g ∘ʲ nul m)
    ≡⟨ refl ⟩
  nul (suc n)
    ≡⟨ refl ⟩
  shift1 g ∘ʲ nul m ▯
∘ʲ-preserves-shift1 {suc l} {suc m} {suc n} (inc c g) (inc b f) =
  shift1 (inc c g ∘ʲ inc b f)
    ≡⟨ refl ⟩
  shift1 (inc (apply (inc c g) b) (remove b (inc c g) ∘ʲ f))
    ≡⟨ refl ⟩
  inc (fsuc (apply (inc c g) b)) (shift1 (remove b (inc c g) ∘ʲ f))
    ≡⟨ cong₂ inc (sym (apply-shift1 (inc c g) b))
                 {!!} ⟩
  inc (apply (inc (fsuc c) (shift1 g)) b) (remove b (inc (fsuc c) (shift1 g)) ∘ʲ f)
    ≡⟨ refl ⟩
  inc (fsuc c) (shift1 g) ∘ʲ inc b f
    ≡⟨ refl ⟩
  shift1 (inc c g) ∘ʲ inc b f ▯

∘ʲ-preserves-shift
  : (k : ℕ) {l m n : ℕ} → (g : Inj m n) (f : Inj l m)
  → (shift k (g ∘ʲ f))
  ≡ (shift k g) ∘ʲ f
∘ʲ-preserves-shift zero {l} {m} {n} g f = refl
∘ʲ-preserves-shift (suc k) {zero} {m} {n} g (nul m) =
  shift (suc k) (g ∘ʲ nul m)
    ≡⟨ refl ⟩
  shift1 (shift k (g ∘ʲ nul m))
    ≡⟨ cong shift1 (∘ʲ-preserves-shift k g (nul m)) ⟩
  shift1 ((shift k g) ∘ʲ nul m)
    ≡⟨ refl ⟩
  shift1 (nul (k + n))
    ≡⟨ refl ⟩
  nul (suc k + n)
    ≡⟨ refl ⟩
  shift (suc k) g ∘ʲ nul m ▯
∘ʲ-preserves-shift (suc k) {suc l} {suc m} {suc n} (inc c g) (inc b f) =
  shift (suc k) (inc c g ∘ʲ inc b f)
    ≡⟨ refl ⟩
  shift1 (shift k (inc c g ∘ʲ inc b f))
    ≡⟨ cong shift1 (∘ʲ-preserves-shift k (inc c g) (inc b f)) ⟩
  shift1 ((shift k (inc c g)) ∘ʲ inc b f)
    ≡⟨ {!!} ⟩
  shift1 ((shift k (inc c g)) ∘ʲ inc b f)
    ≡⟨ {!!} ⟩
  shift (suc k) (inc (apply (inc c g) b) (remove b (inc c g) ∘ʲ f))
    ≡⟨ {!!} ⟩
  inc (apply (shift (suc k) (inc c g)) b) (remove b (shift (suc k) (inc c g)) ∘ʲ f)
    ≡⟨ refl ⟩
  shift (suc k) (inc c g) ∘ʲ inc b f ▯

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
⊕-preserves-∘ {zero} {zero} {zero} {suc n} {suc n'} {suc n''}
              (nul zero) (nul zero) (inc b g) (inc b' g') =
  (nul zero ∘ʲ nul zero) ⊕ (inc b' g' ∘ʲ inc b g)
    ≡⟨ refl ⟩
  nul zero ⊕ (inc b' g' ∘ʲ inc b g)
    ≡⟨ refl ⟩
  inc b' g' ∘ʲ inc b g
    ≡⟨ refl ⟩
  (nul zero ⊕ inc b' g') ∘ʲ (nul zero ⊕ inc b g) ▯
⊕-preserves-∘ {zero} {zero} {suc m''} {suc n} {suc n'} {suc n''}
              (nul zero) (nul (suc m'')) (inc b g) (inc b' g') =
  (nul (suc m'') ∘ʲ nul zero) ⊕ (inc b' g' ∘ʲ inc b g)
    ≡⟨ refl ⟩
  nul (suc m'') ⊕ (inc b' g' ∘ʲ inc b g)
    ≡⟨ refl ⟩
  shift1 (shift m'' (inc b' g' ∘ʲ inc b g))
    ≡⟨ {!!} ⟩
  shift1 (shift m'' (inc b' g')) ∘ʲ inc b g
    ≡⟨ refl ⟩
  shift (suc m'') (inc b' g') ∘ʲ inc b g
    ≡⟨ refl ⟩
  (nul (suc m'') ⊕ inc b' g') ∘ʲ (nul zero ⊕ inc b g) ▯
  where
    p = +-suc zero n'
    q = +-suc (suc m'') n''
⊕-preserves-∘ {zero} {zero} {m''} {suc n} {suc n'} {suc n''} (nul zero) (nul m'') (inc b g) g' =
  (nul m'' ∘ʲ nul zero) ⊕ (g' ∘ʲ inc b g)
    ≡⟨ refl ⟩
  nul m'' ⊕ inc (apply g' b) (remove b g' ∘ʲ g)
    ≡⟨ {!!} ⟩
  ((nul m'' ⊕ g') ∘ʲ inc b g)
    ≡⟨ {!!} ⟩
  ((nul m'' ⊕ g') ∘ʲ (nul zero ⊕ inc b g)) ▯
  where
    p = +-suc zero n'
    q = +-suc m'' n''
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
    ≡⟨ {!!} ⟩
  subst2 Inj refl (sym q)
         (inc (apply (subst2 Inj p q (f' ⊕ g')) (subst Fin p (fshift m' b)))
              (remove (subst Fin p (fshift m' b)) (subst2 Inj p q (f' ⊕ g'))
              ∘ʲ (shift' m' g)))
    ≡⟨ {!!} ⟩
  subst2 Inj refl (sym q)
         (subst2 Inj p q (f' ⊕ g')
         ∘ʲ subst (Inj (suc n)) p (subst (Inj (suc n)) (sym p)
            (inc (subst Fin p (fshift m' b)) (shift' m' g))))
    ≡⟨  cong (λ ○ → subst2 Inj refl (sym q)
         (subst2 Inj p q (f' ⊕ g')
         ∘ʲ ○)) (subst-filler (Inj (suc n)) (λ i → suc (m' + n')) {!!})  ⟩
  subst2 Inj refl (sym q)
         (subst2 Inj p q (f' ⊕ g')
         ∘ʲ inc (subst Fin p (fshift m' b)) (shift' m' g))
    ≡⟨ u ⟩
  (f' ⊕ g') ∘ʲ subst2 Inj refl (sym p) (inc (subst Fin p (fshift m' b)) (shift' m' g))
    ≡⟨ cong ((f' ⊕ g') ∘ʲ_) (sym (shift≡shift' m' (inc b g))) ⟩
  (f' ⊕ g') ∘ʲ shift m' (inc b g)
    ≡⟨ refl ⟩
  (f' ⊕ g') ∘ʲ (nul m' ⊕ inc b g) ▯
  where
    p = +-suc m' n'
    q = +-suc m'' n''
    u : {!inc (subst Fin p (fshift m' b)) (shift' m' g) ≡!}
⊕-preserves-∘ {suc m} {suc m'} {m''} {zero} {n'} {n''} (inc b f) f' (nul .n') g' = {!!}
⊕-preserves-∘ {m} {m'} {m''} {n} {n'} {n''} (inc b f) f' (inc b₁ g) g' = {!!}

