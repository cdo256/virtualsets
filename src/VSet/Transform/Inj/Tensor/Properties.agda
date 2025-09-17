module VSet.Transform.Inj.Tensor.Properties where

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
open import VSet.Transform.Inj.Elementary.Base
open import VSet.Transform.Inj.Inverse.Base
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Tensor.Base
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


Id⊕Id≡Id : Id {m} ⊕ Id {n} ≡ Id {m + n}
Id⊕Id≡Id {zero} {n} = refl
Id⊕Id≡Id {suc m} {n} = cong (inc f0) (Id⊕Id≡Id {m} {n})

nul-⊕-nul : {m n : ℕ} → nul m ⊕ nul n ≡ nul (m + n)
nul-⊕-nul {zero} = refl
nul-⊕-nul {suc m} {n} =
  shift (suc m) (nul n) ≡⟨ refl ⟩
  shift1 (shift m (nul n)) ≡⟨ cong shift1 (nul-⊕-nul {m} {n}) ⟩
  nul (suc m + n) ▯

∘ʲ-nul : {m n : ℕ} → (f : Inj m n) → f ∘ʲ nul m ≡ nul n
∘ʲ-nul f = refl

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

remove-shift1 : {m n : ℕ} → (f : Inj (suc m) (suc n)) (a : Fin (suc m))
              → remove a (shift1 f) ≡ shift1 (remove a f)
remove-shift1 {m} {n} (inc b f) fzero = refl
remove-shift1 {zero} {n} (inc b (nul .n)) (fsuc ())
remove-shift1 {suc m} {suc n} (inc b f) (fsuc a) =
  remove (fsuc a) (shift1 (inc b f))
    ≡⟨ refl ⟩
  remove (fsuc a) (inc (fsuc b) (shift1 f))
    ≡⟨ refl ⟩
  inc (fcross (apply (shift1 f) a) (fsuc b)) (remove a (shift1 f))
    ≡⟨ cong₂ inc (cong (λ ○ → fcross ○ (fsuc b)) (apply-shift1 f a))
                 (remove-shift1 f a) ⟩
  inc (fsuc (fcross (apply f a) b)) (shift1 (remove a f))
    ≡⟨ refl ⟩
  shift1 (inc (fcross (apply f a) b) (remove a f))
    ≡⟨ refl ⟩
  shift1 (remove (fsuc a) (inc b f)) ▯

∘ʲ-preserves-shift1
  : {l m n : ℕ} → (g : Inj m n) (f : Inj l m)
  → shift1 (g ∘ʲ f)
  ≡ (shift1 g) ∘ʲ f

shift1-remove-comp
  : {l m n : ℕ} (f : Inj l m) (g : Inj m n) (d : Fin (suc m)) (c : Fin (suc n))
  → shift1 (remove d (inc c g) ∘ʲ f)
  ≡ remove d (inc (fsuc c) (shift1 g)) ∘ʲ f

shift1-remove-comp {zero} {m} {n} (nul m) g d c = refl
shift1-remove-comp {suc l} {suc m} {suc n} (inc b f) g fzero c =
  shift1 (remove fzero (inc c g) ∘ʲ inc b f)
    ≡⟨ refl ⟩
  shift1 (g ∘ʲ inc b f)
    ≡⟨ ∘ʲ-preserves-shift1 g (inc b f) ⟩
  (shift1 g) ∘ʲ inc b f
    ≡⟨ refl ⟩
  remove fzero (inc (fsuc c) (shift1 g)) ∘ʲ inc b f ▯
shift1-remove-comp {suc l} {suc m} {suc n} (inc b f) g (fsuc d) c =
  shift1 (remove (fsuc d) (inc c g) ∘ʲ inc b f)
    ≡⟨ refl ⟩
  shift1 (inc (apply (remove (fsuc d) (inc c g)) b)
              (remove b (remove (fsuc d) (inc c g)) ∘ʲ f))
    ≡⟨ refl ⟩
  inc (fsuc (apply (remove (fsuc d) (inc c g)) b))
      (shift1 (remove b (remove (fsuc d) (inc c g)) ∘ʲ f))
    ≡⟨ cong₂ inc (u b c d) (v b c d f) ⟩
  inc (apply (inc (fcross (apply (shift1 g) d) (fsuc c))
                  (remove d (shift1 g))) b)
      (remove b (inc (fcross (apply (shift1 g) d) (fsuc c))
                             (remove d (shift1 g))) ∘ʲ f) 
    ≡⟨ refl ⟩
     inc (fcross (apply (shift1 g) d) (fsuc c)) (remove d (shift1 g))
  ∘ʲ inc b f
    ≡⟨ refl ⟩
  remove (fsuc d) (inc (fsuc c) (shift1 g)) ∘ʲ inc b f ▯
  where
    u : ∀ b c d
      → fsuc (apply (remove (fsuc d) (inc c g)) b)
      ≡ apply (inc (fcross (apply (shift1 g) d) (fsuc c))
                   (remove d (shift1 g))) b
    u fzero c d =
      fsuc (apply (remove (fsuc d) (inc c g)) fzero)
        ≡⟨ refl ⟩
      fsuc (apply (inc (fcross (apply g d) c) (remove d g)) fzero)
        ≡⟨ refl ⟩
      fsuc (fcross (apply g d) c)
        ≡⟨ refl ⟩
      fcross (fsuc (apply g d)) (fsuc c)
        ≡⟨ cong (λ ○ → fcross ○ (fsuc c)) (sym (apply-shift1 g d)) ⟩
      fcross (apply (shift1 g) d) (fsuc c)
        ≡⟨ refl ⟩
      apply (inc (fcross (apply (shift1 g) d) (fsuc c))
                   (remove d (shift1 g))) fzero ▯
    u (fsuc b) c d =
      fsuc (apply (remove (fsuc d) (inc c g)) (fsuc b))
        ≡⟨ refl ⟩
      fsuc (fsplice (fcross (apply g d) c) (apply (remove d g) b))
        ≡⟨ refl ⟩
      fsplice (fcross (fsuc (apply g d)) (fsuc c))
              (fsuc (apply (remove d g) b))
        ≡⟨ cong (fsplice (fcross (fsuc (apply g d)) (fsuc c)))
                ( sym (apply-shift1 (remove d g) b)
                ∙ (sym $ cong (λ ○ → apply ○ b) (remove-shift1 g d))) ⟩
      fsplice (fcross (fsuc (apply g d)) (fsuc c))
              (apply (remove d (shift1 g)) b)
        ≡⟨ cong (λ ○ → fsplice (fcross ○ (fsuc c)) (apply (remove d (shift1 g)) b))
                (sym (apply-shift1 g d)) ⟩
      apply (inc (fcross (apply (shift1 g) d) (fsuc c))
                 (remove d (shift1 g))) (fsuc b) ▯
    v : ∀ b c d f
      → shift1 (remove b (remove (fsuc d) (inc c g)) ∘ʲ f)
      ≡ remove b (inc (fcross (apply (shift1 g) d) (fsuc c))
                      (remove d (shift1 g))) ∘ʲ f
    v b c d f =
      shift1 (remove b (remove (fsuc d) (inc c g)) ∘ʲ f)
        ≡⟨ refl ⟩
      shift1 (remove b (inc (fcross (apply g d) c) (remove d g)) ∘ʲ f)
        ≡⟨ shift1-remove-comp f (remove d g) b (fcross (apply g d) c) ⟩
      remove b (inc (fsuc (fcross (apply g d) c)) (shift1 (remove d g))) ∘ʲ f
        ≡⟨ cong (λ ○ → remove b ○ ∘ʲ f)
                (cong₂ inc (cong₂ fcross (sym (apply-shift1 g d)) refl)
                           (sym (remove-shift1 g d))) ⟩
      remove b (inc (fcross (apply (shift1 g) d) (fsuc c)) (remove d (shift1 g)))
        ∘ʲ f ▯

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
                 (shift1-remove-comp f g b c) ⟩
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
  shift1 (shift k (inc c g) ∘ʲ inc b f)
    ≡⟨ ∘ʲ-preserves-shift1 (shift k (inc c g)) (inc b f) ⟩
  shift1 (shift k (inc c g)) ∘ʲ inc b f
    ≡⟨ refl ⟩
  shift (suc k) (inc c g) ∘ʲ inc b f ▯

peel-l : (k : ℕ) {m n : ℕ} (f : Inj (k + m) n) → Inj m n
peel-l zero f = f
peel-l (suc k) {n = suc n} f = peel-l k (excise f0 f)

peel-r : (k : ℕ) {m n : ℕ} (f : Inj (m + k) n) → Inj m n
peel-r zero {m} {n} f = jcast (+-zero m) refl f
peel-r (suc k) {zero} {n} f = nul n
peel-r (suc k) {suc m} {suc n} f = peel-r k (jcast (+-suc m k) refl (excise fmax f))

-- tensor-comp-shift : {m m' m'' n n' n'' : ℕ} (g : Inj m n) (h : Inj k k') (f : Inj l m)
--                   → toℕ c < k
--                   → g ∘ʲ shift (suc k) f ≡ shift k (g ∘ʲ f)
-- tensor-comp-shift {zero} {m} {n} g c (nul _) = refl
-- tensor-comp-shift {suc l} {suc m} {suc n} g c (inc b f) =
--   inc c g ∘ʲ shift1 (inc b f)
--     ≡⟨ refl ⟩
--   inc c g ∘ʲ inc (fsuc b) (shift1 f)
--     ≡⟨ {!!} ⟩
--   inc (apply (inc c g) (fsuc b)) (remove (fsuc b) (inc c g) ∘ʲ shift1 f)
--     ≡⟨ {!!} ⟩
--   inc (fsuc (apply g b)) (shift1 (remove b g ∘ʲ f))
--     ≡⟨ refl ⟩
--   shift1 (inc (apply g b) (remove b g ∘ʲ f))
--     ≡⟨ refl ⟩
--   shift1 (g ∘ʲ inc b f) ▯


-- inc-comp-shift : (k : ℕ) {l m n : ℕ} (g : Inj (k + m) n) (c : Fin (suc n)) (f : Inj l m)
--                → toℕ c < k
--                → inc c g ∘ʲ shift (suc k) f ≡ shift (suc k) (g ∘ʲ f)
-- inc-comp-shift {zero} {m} {n} g c (nul _) = refl
-- inc-comp-shift {suc l} {suc m} {suc n} g c (inc b f) =
--   inc c g ∘ʲ shift1 (inc b f)
--     ≡⟨ refl ⟩
--   inc c g ∘ʲ inc (fsuc b) (shift1 f)
--     ≡⟨ {!!} ⟩
--   inc (apply (inc c g) (fsuc b)) (remove (fsuc b) (inc c g) ∘ʲ shift1 f)
--     ≡⟨ {!!} ⟩
--   inc (fsuc (apply g b)) (shift1 (remove b g ∘ʲ f))
--     ≡⟨ refl ⟩
--   shift1 (inc (apply g b) (remove b g ∘ʲ f))
--     ≡⟨ refl ⟩
--   shift1 (g ∘ʲ inc b f) ▯

⊕-peel-l : {m m' m'' n n' n'' : ℕ} (f' : Inj m' m'')
         → (g : Inj (suc n) (suc n')) (g' : Inj (suc n') (suc n''))
         → shift m'' (g' ∘ʲ g) ≡ (f' ⊕ g') ∘ʲ shift m' g 
⊕-peel-l {m' = zero} {m'' = m''} (nul m'') g g' =
  shift m'' (g' ∘ʲ g)
    ≡⟨ ∘ʲ-preserves-shift m'' g' g ⟩
  (shift m'' g') ∘ʲ g
    ≡⟨ refl ⟩
  (nul m'' ⊕ g') ∘ʲ g ▯
⊕-peel-l {m' = suc m'} {m'' = suc m''} {n'' = n''} (inc b f') g g' =
  shift (suc m'') (g' ∘ʲ g)
    ≡⟨ {!!} ⟩
  (inc (finject (suc n'') b) (f' ⊕ g')) ∘ʲ shift (suc m') g
    ≡⟨ refl ⟩
  (inc b f' ⊕ g') ∘ʲ shift (suc m') g ▯

⊕-preserves-∘ : ∀ {m m' m'' n n' n''}
              → (f : Inj m m') (f' : Inj m' m'') (g : Inj n n') (g' : Inj n' n'')
              → (f' ∘ʲ f) ⊕ (g' ∘ʲ g) ≡ (f' ⊕ g') ∘ʲ (f ⊕ g)
⊕-preserves-∘ {zero} {suc m'} {m''} {zero} {n'} {n''} (nul (suc m')) f' (nul n') g' =
  (f' ∘ʲ nul (suc m')) ⊕ (g' ∘ʲ nul n')
    ≡⟨ refl ⟩
  (nul m'') ⊕ (nul n'')
    ≡⟨ nul-⊕-nul {m''} ⟩
  nul (m'' + n'')
    ≡⟨ refl ⟩
  (f' ⊕ g') ∘ʲ nul ((suc m') + n')
    ≡⟨ cong (tensor f' g' ∘ʲ_) (sym (nul-⊕-nul {suc m'})) ⟩
  (f' ⊕ g') ∘ʲ (nul (suc m') ⊕ nul n') ▯
⊕-preserves-∘ {zero} {zero} {m''} {n} {n'} {n''}
              (nul zero) (nul m'') g g' =
  (nul m'' ∘ʲ nul zero) ⊕ (g' ∘ʲ g)
    ≡⟨ refl ⟩
  nul m'' ⊕ (g' ∘ʲ g)
    ≡⟨ refl ⟩
  shift m'' (g' ∘ʲ g)
    ≡⟨ ∘ʲ-preserves-shift m'' g' g ⟩
  shift m'' g' ∘ʲ g
    ≡⟨ refl ⟩
  (nul m'' ⊕ g') ∘ʲ (nul zero ⊕ g) ▯
-- ⊕-preserves-∘ {zero} {m'} {m''} {suc n} {suc n'} {suc n''} (nul m') f' (inc b g) g' =
--   (f' ∘ʲ nul m') ⊕ (g' ∘ʲ inc b g)
--     ≡⟨ refl ⟩
--   nul m'' ⊕ inc (apply g' b) (remove b g' ∘ʲ g)
--     ≡⟨ refl ⟩
--   shift m'' (inc (apply g' b) (remove b g' ∘ʲ g))
--     ≡⟨ shift≡shift' m'' (inc (apply g' b) (remove b g' ∘ʲ g)) ⟩
--   shift' m'' (inc (apply g' b) (remove b g' ∘ʲ g))
--     ≡⟨ refl ⟩
--   subst2 Inj refl (sym q)
--          (inc (subst Fin q (fshift m'' (apply g' b)))
--               (shift' m'' (remove b g' ∘ʲ g)))
--     ≡⟨ {!!} ⟩
--   subst2 Inj refl (sym q)
--          (inc (apply (subst2 Inj p q (f' ⊕ g')) (subst Fin p (fshift m' b)))
--               (remove (subst Fin p (fshift m' b)) (subst2 Inj p q (f' ⊕ g'))
--               ∘ʲ (shift' m' g)))
--     ≡⟨ {!!} ⟩
--   subst2 Inj refl (sym q)
--          (subst2 Inj p q (f' ⊕ g')
--          ∘ʲ subst (Inj (suc n)) p (subst (Inj (suc n)) (sym p)
--             (inc (subst Fin p (fshift m' b)) (shift' m' g))))
--     ≡⟨  cong (λ ○ → subst2 Inj refl (sym q)
--          (subst2 Inj p q (f' ⊕ g')
--          ∘ʲ ○)) (subst-filler (Inj (suc n)) (λ i → suc (m' + n')) {!!})  ⟩
--   subst2 Inj refl (sym q)
--          (subst2 Inj p q (f' ⊕ g')
--          ∘ʲ inc (subst Fin p (fshift m' b)) (shift' m' g))
--     ≡⟨ u ⟩
--   (f' ⊕ g') ∘ʲ subst2 Inj refl (sym p) (inc (subst Fin p (fshift m' b)) (shift' m' g))
--     ≡⟨ cong ((f' ⊕ g') ∘ʲ_) (sym (shift≡shift' m' (inc b g))) ⟩
--   (f' ⊕ g') ∘ʲ shift m' (inc b g)
--     ≡⟨ refl ⟩
--   (f' ⊕ g') ∘ʲ (nul m' ⊕ inc b g) ▯
--   where
--     p = +-suc m' n'
--     q = +-suc m'' n''

⊕-preserves-∘ {zero} {suc m'} {suc m''} {suc n} {suc n'} {suc n''}
              (nul (suc m')) (inc b' f') (inc c g) g' =
  (inc b' f' ∘ʲ nul (suc m')) ⊕ (g' ∘ʲ inc c g)
    ≡⟨ refl ⟩
  nul (suc m'') ⊕ (g' ∘ʲ inc c g)
    ≡⟨ refl ⟩
  shift (suc m'') (g' ∘ʲ inc c g)
    ≡⟨ refl ⟩
  shift1 (shift m'' (g' ∘ʲ inc c g))
    ≡⟨ cong shift1 (shift≡shift' m'' (g' ∘ʲ inc c g)) ⟩
  shift1 (shift' m'' (g' ∘ʲ inc c g))
    ≡⟨ {!!} ⟩
  inc (finject _ b') (f' ⊕ g') ∘ʲ shift1 (shift' m' (inc c g))
    ≡⟨ cong (inc (finject _ b') (f' ⊕ g') ∘ʲ_ ∘ shift1)
            (sym (shift≡shift' m' (inc c g))) ⟩
  inc (finject _ b') (f' ⊕ g') ∘ʲ shift1 (shift m' (inc c g))
    ≡⟨ refl ⟩
  inc (finject _ b') (f' ⊕ g') ∘ʲ shift (suc m') (inc c g)
    ≡⟨ refl ⟩
  (inc b' f' ⊕ g') ∘ʲ shift (suc m') (inc c g)
    ≡⟨ refl ⟩
  (inc b' f' ⊕ g') ∘ʲ (nul (suc m') ⊕ inc c g) ▯
⊕-preserves-∘ {suc m} {suc m'} {m''} {zero} {n'} {n''} (inc b f) f' (nul .n') g' = {!!}
⊕-preserves-∘ {m} {m'} {m''} {n} {n'} {n''} (inc b f) f' (inc b₁ g) g' = {!!}
