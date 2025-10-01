module VSet.Data.Inj.Properties where

open import VSet.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Data.Sum.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.List.Base hiding (elim; [_])
open import Cubical.Data.Maybe.Base hiding (elim)
open import VSet.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import Cubical.Foundations.GroupoidLaws
open import VSet.Function.Injection

private
  variable
    l l' m m' n n' : ℕ

apply-Inj-isInjective : (f : Inj m n) → is-injective (apply f)
apply-Inj-isInjective f fzero fzero fx≡fy = refl
apply-Inj-isInjective (inc b f) fzero (fsuc y) fx≡fy =
  absurd (fsplice≉b b (apply f y) (≡→≈ᶠ (sym fx≡fy)))
apply-Inj-isInjective (inc b f) (fsuc x) fzero fx≡fy =
  absurd (fsplice≉b b (apply f x) (≡→≈ᶠ fx≡fy))
apply-Inj-isInjective (inc b f) (fsuc x) (fsuc y) fx≡fy =
  cong fsuc (apply-Inj-isInjective f x y (fsplice-isInjective fx≡fy))

subst2-inc-reorder 
  : ∀ {m m' n n'} (p : m ≡ n) (q : m' ≡ n')
  → (a : Fin (suc m'))
  → (f : Inj m m')
  → subst2 Injsuc p q (inc a f)
  ≡ inc (subst (Fin ∘ suc) q a) (subst2 Inj p q f)
subst2-inc-reorder {m} {m'} {n} {n'} p q a f =
  let b : Fin (suc n')
      b = subst (Fin ∘ suc) q a
      r : (λ i → Fin (suc (q i))) [ a ≡ b ]
      r = transport-filler (λ i → Fin (suc (q i))) a
      g : Inj n n'
      g = subst2 Inj p q f
      s : (λ i → Inj (p i) (q i)) [ f ≡ g ]
      s = transport-filler (λ i → Inj (p i) (q i)) f
      step1 : (λ i → cong₂ Injsuc p q i)
            [ inc {m} {m'} a f ≡ inc {n} {n'} b g ]
      step1 i = inc {p i} {q i} (r i) (s i)
      step2 : (λ i → cong₂ Injsuc p q i)
            [ inc a f
            ≡ subst2 Injsuc p q (inc a f)
            ]
      step2 = transport-filler (λ i → Injsuc (p i) (q i)) (inc a f)
      composite : (λ i → Injsuc ((sym p ∙ p) i) ((sym q ∙ q) i))
        [ inc b g
        ≡ subst2 Injsuc p q (inc a f)
        ]
      -- This actually isn't directly applicable.
      composite = compPathP' step1 step2
  in sym (subst2 (λ ○ □ → PathP (λ i → (Injsuc (○ i) (□ i)))
                          (inc b g) (subst2 Injsuc p q (inc a f)))
           (lCancel p) (lCancel q) composite)

subst2-inc-reorder'
  : ∀ {m m' n n'} (p : suc m ≡ suc n) (q : suc m' ≡ suc n')
  → (a : Fin (suc m'))
  → (f : Inj m m')
  → subst2 Inj p q (inc a f)
  ≡ inc (subst Fin q a) (subst2 Inj (cong predℕ p) (cong predℕ q) f)
subst2-inc-reorder' {m} {m'} {n} {n'} p q a f =
  subst2 Inj p q (inc a f)
    ≡⟨ cong₂ (λ ○ □ → subst2 Inj ○ □ (inc a f))
             (sym (path-suc-pred p)) (sym (path-suc-pred q)) ⟩
  subst2 Inj (cong (suc ∘ predℕ) p) (cong (suc ∘ predℕ) q) (inc a f) 
    ≡⟨ subst2-inc-reorder (cong predℕ p) (cong predℕ q) a f ⟩
  inc (subst Fin (cong (suc ∘ predℕ) q) a) (subst2 Inj (cong predℕ p) (cong predℕ q) f)
    ≡⟨ cong (λ ○ → inc (subst Fin ○ a) (subst2 Inj (cong predℕ p) (cong predℕ q) f))
            (path-suc-pred q) ⟩
  inc (subst Fin q a) (subst2 Inj (cong predℕ p) (cong predℕ q) f) ▯

subst2≡jcast : ∀ {m m' n n' : ℕ} → (p : m ≡ m') → (q : n ≡ n') → (f : Inj m n)
             → subst2 Inj p q f ≡ jcast p q f
subst2≡jcast {zero} {zero} {n} {n'} p q (nul n) =
  s ∙ r 
  where
    r : subst (Inj 0) q (nul n) ≡ nul n'
    r = sym (resubst (Inj 0) nul q)
    s : subst2 Inj p q (nul n) ≡ subst2 Inj refl q (nul n)
    s = cong (λ ○ → subst2 Inj ○ q (nul n)) (isSetℕ 0 0 p refl)
subst2≡jcast {zero} {suc m'} {n} {n'} p q (nul n) = absurd (znots p)
subst2≡jcast {suc m} {zero} {suc n} {n'} p q (inc b f) = absurd (snotz p)
subst2≡jcast {suc m} {suc m'} {suc n} {zero} p q (inc b f) = absurd (snotz q)
subst2≡jcast {suc m} {suc m'} {suc n} {suc n'} p q (inc b f) =
  subst2 Inj p q (inc b f)
    ≡⟨ cong₂ (λ ○ □ → subst2 {x = suc m} {y = suc m'} {z = suc n} {w = suc n'}
                             Inj ○ □ (inc b f))
             (sym (path-suc-pred p))
             (sym (path-suc-pred q)) ⟩
  subst2 Injsuc p' q' (inc b f)
    ≡⟨ subst2-inc-reorder p' q' b f ⟩
  inc (subst (Fin ∘ suc) q' b)
      (subst2 Inj (injSuc p) (injSuc q) f)
    ≡⟨ cong₂ inc (subst≡fcast (cong suc q') b
                 ∙ cong (λ ○ → fcast ○ b) (path-suc-pred q))
                 (subst2≡jcast p' q' f) ⟩
  inc (fcast q b)
      (jcast p' q' f) ▯
  where
    p' = injSuc p
    q' = injSuc q

nul≡subst-nul : {m n : ℕ} (p : m ≡ n) → nul n ≡ subst (Inj 0) p (nul m)
nul≡subst-nul {m} {n} p = resubst (Inj 0) nul p

nul≡subst2-nul : {m n : ℕ} (p : 0 ≡ 0) (q : m ≡ n)
               → nul n ≡ subst2 Inj p q (nul m)
nul≡subst2-nul {m} {n} p q =
  nul n
    ≡⟨ nul≡subst-nul q ⟩
  subst2 Inj refl q (nul m)
    ≡⟨ cong (λ ○ → subst2 Inj ○ q (nul m)) (isSetℕ 0 0 refl p) ⟩
  subst2 Inj p q (nul m) ▯

subst2-inc-β :
  ∀ {l m n} (p : l ≡ m) (b : Fin (suc n)) (f : Inj l n) →
  subst2 Inj (cong suc p) refl (inc b f) ≡ inc b (subst2 Inj (p) refl f)
subst2-inc-β p b f = subst2-inc-reorder p refl b f
                   ∙ cong (λ ○ → inc ○ (subst2 Inj p refl f))
                          (transportRefl b)

subst-apply-reorder
  : (x : Fin l) (f : Inj m n) (p : l ≡ m)
  → apply f (subst Fin p x)
    ≡ apply (subst2 Inj (sym p) refl f) x
subst-apply-reorder {suc l} {zero} {n} x (nul n) p = absurd (snotz p)
subst-apply-reorder {zero} {suc m} {suc n} x (inc b f) p = absurd (znots p)
subst-apply-reorder {zero} {zero} {n} () (nul n) p
subst-apply-reorder {suc l} {suc m} {suc n} fzero (inc b f) p =
  apply (inc b f) (subst Fin p (f0 {l}))
    ≡⟨ cong (apply (inc b f)) (sym (fzero≡subst-fzero' p)) ⟩
  apply (inc b f) (f0 {m}) 
    ≡⟨ refl ⟩
  b
    ≡⟨ sym (transportRefl b) ⟩
  subst Fin refl b
    ≡⟨ refl ⟩
  apply (inc (subst Fin refl b)
        (subst2 Inj (cong predℕ (sym p)) refl f)) f0
    ≡⟨ cong (λ ○ → apply ○ (f0 {l})) (sym (subst2-inc-reorder' (sym p) refl b f)) ⟩
  apply (subst2 Inj (sym p) refl (inc b f)) (f0 {l}) ▯
subst-apply-reorder {suc l} {suc m} {suc n} (fsuc x) (inc b f) p =
  apply (inc b f) (subst Fin p (fsuc x))
    ≡⟨ cong (λ ○ → apply (inc b f) (subst Fin ○ (fsuc x))) (sym (path-suc-pred p)) ⟩
  apply (inc b f) (subst Fin (cong (suc ∘ predℕ) p) (fsuc x))
    ≡⟨ cong (apply (inc b f)) refl ⟩
  apply (inc b f) (fsuc (subst Fin (cong predℕ p) x)) 
    ≡⟨ refl ⟩
  fsplice b (apply f (subst Fin (cong predℕ p) x))
    ≡⟨ cong₂ fsplice (sym (transportRefl b)) (subst-apply-reorder x f (cong predℕ p)) ⟩
  fsplice (subst Fin refl b)
          (apply (subst2 Inj (cong predℕ (sym p)) refl f) x)
    ≡⟨ refl ⟩
  apply (inc (subst Fin refl b)
        (subst2 Inj (cong predℕ (sym p)) refl f)) (fsuc x)
    ≡⟨ cong (λ ○ → apply ○ (fsuc x)) (sym (subst2-inc-reorder' (sym p) refl b f)) ⟩
  apply (subst2 Inj (sym p) refl (inc b f)) (fsuc x) ▯
