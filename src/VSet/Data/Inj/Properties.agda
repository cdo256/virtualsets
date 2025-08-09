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

