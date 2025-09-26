module VSet.Transform.Inj.Trace.Superimposing where

open import Cubical.Data.Maybe.Base hiding (elim)
-- open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Properties
-- open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base renaming (pred to fpred)
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base 
-- open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
-- open import VSet.Data.Maybe
-- open import VSet.Data.Nat.Properties
open import VSet.Prelude
-- open import VSet.Transform.Inj.Compose.Base
-- open import VSet.Transform.Inj.Elementary.Base 
open import VSet.Transform.Inj.Inverse.Base 
-- open import VSet.Transform.Inj.Inverse.Insert
-- open import VSet.Transform.Inj.Inverse.Properties
-- open import VSet.Transform.Inj.Tensor.Associator 
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties
open import VSet.Transform.Inj.Trace.Base
open import VSet.Transform.Inj.Trace.Properties using (fin-restrict≡subst)


private
  variable
    k k' l l' m m' n n' : ℕ
    A B C D U V W X Y Z : ℕ


apply-inv≡nothing
  : {l m n : ℕ} (b : Fin l) (c : Fin (suc n)) (g : Inj m n)
  → apply-inv (shift l (inc c g)) (subst Fin (λ i → +-suc l n (~ i)) f0)
  ≡ nothing
apply-inv≡nothing {suc l} {suc m} {suc n} b c (inc d g) =
  -- apply-inv (shift (suc l) (inc c (inc d g)))
  --  (subst Fin (sym (+-suc (suc l) (suc n))) f0)
  --   ≡⟨ cong (apply-inv (shift (suc l) (inc c (inc d g))))
  --           (sym (fzero≡subst-fzero ((sym (+-suc l (suc n)))))) ⟩
  -- apply-inv (shift (suc l) (inc c (inc d g))) f0
  --   ≡⟨ cong (λ ○ → apply-inv ○ f0) (shift≡shift' (suc l) (inc c (inc d g))) ⟩ 
  -- apply-inv (shift' (suc l) (inc c (inc d g))) f0
  --   ≡⟨ refl ⟩
  -- apply-inv (subst2 Inj refl (sym (+-suc (suc l) (suc n)))
  --            (inc (subst Fin (+-suc (suc l) (suc n)) (fshift (suc l) c))
  --                 (shift' (suc l) (inc d g)))) f0
  --   ≡⟨ cong (λ ○ → apply-inv ○ f0) (subst2-inc-reorder refl (sym (+-suc l (suc n)))
  --                (subst Fin (+-suc (suc l) (suc n)) (fshift (suc l) c))
  --                (shift' (suc l) (inc d g))) ⟩
  apply-inv (inc (subst Fin (sym (+-suc (suc l) (suc n))) (subst Fin (+-suc (suc l) (suc n)) (fshift (suc l) c)))
                 (subst2 Inj refl (sym (+-suc l (suc n))) (shift' (suc l) (inc d g)))) f0
    ≡⟨ cong (λ ○ → apply-inv (inc ○ (subst2 Inj refl (sym (+-suc l (suc n))) (shift' (suc l) (inc d g))) f0)) (subst⁻Subst Fin (+-suc (suc l) (suc n)) (fshift (suc l) c)) ⟩
  apply-inv (inc (fshift (suc l) c)
                 (subst2 Inj refl (sym (+-suc l (suc n))) (shift' (suc l) (inc d g)))) f0
    ≡⟨ {!!} ⟩
  nothing ▯
apply-inv≡nothing {suc l} {zero} {n} b c (nul _) = {!!}
  -- apply-inv (shift (suc l) (inc c (nul _))) (subst Fin (sym (+-suc (suc l) n)) f0)
  --   ≡⟨ refl ⟩
  -- apply-inv (shift (suc l) (inc c (nul _))) (subst (Fin ∘ suc) (sym (+-suc l n)) f0)
  --   ≡⟨ cong (apply-inv (shift (suc l) (inc c (nul _))))
  --           (sym (fzero≡subst-fzero (sym (+-suc l n)))) ⟩
  -- apply-inv (shift (suc l) (inc c (nul _))) f0
  --   ≡⟨ cong (λ ○ → apply-inv ○ f0)
  --           (shift≡shift' (suc l) (inc c (nul _)))  ⟩
  -- apply-inv (shift' (suc l) (inc c (nul _))) f0
  --   ≡⟨ refl ⟩
  -- apply-inv (subst2 Inj refl (sym (+-suc (suc l) n))
  --   (inc (subst Fin (+-suc (suc l) n) (fshift (suc l) c)) (shift' (suc l) (nul _)))) f0
  --   ≡⟨ cong (λ ○ → apply-inv ○ f0)
  --           (subst2-inc-reorder refl (sym (+-suc l n))
  --            (subst Fin (+-suc (suc l) n) (fshift (suc l) c))
  --            (shift' (suc l) (nul _))) ⟩
  -- apply-inv (inc d h) f0
  --   ≡⟨ cong (λ ○ → apply-inv (inc ○ h) f0) d≡e ⟩
  -- apply-inv (inc e h) f0
  --   ≡⟨ refl ⟩
  -- apply-inv-rec h e f0 (no fzero≉fsuc)
  --   ≡⟨ refl ⟩
  -- map-Maybe fsuc (apply-inv h (fjoin e f0 fzero≉fsuc))
  --   ≡⟨ cong₂ (λ ○ □ → map-Maybe fsuc (apply-inv h (fjoin ○ f0 □)))
  --            refl (λ i → subst (f0 {l + suc n} ≉ᶠ_)
  --                              (λ j → e≡e' (~ (i ∧ j)))
  --                              fzero≉fsuc) ⟩
  -- map-Maybe fsuc (apply-inv h (fjoin (fsuc (fshift l c)) f0 fzero≉fsuc))
  --   ≡⟨ cong
  --       (λ ○ → map-Maybe fsuc
  --        (apply-inv ○ (fjoin (fsuc (fshift l c)) f0 fzero≉fsuc)))
  --       h≡nul ⟩
  -- map-Maybe fsuc (apply-inv (nul (l + suc n)) (fjoin (fsuc (fshift l c)) f0 fzero≉fsuc))
  --   ≡⟨ cong (map-Maybe fsuc) refl ⟩
  -- map-Maybe fsuc nothing
  --   ≡⟨ refl ⟩
  -- nothing ▯
  -- where
  --   q : l + suc n ≡ suc (l + n) 
  --   q = +-suc l n
  --   d : Fin (suc (l + suc n))
  --   d = subst (Fin ∘ suc) (sym (+-suc l n))
  --             (subst Fin (+-suc (suc l) n) (fshift (suc l) c))
  --   e : Fin (suc (l + suc n))
  --   e = fsuc (fshift l c)
  --   e≡e' : e ≡ fsuc (fshift l c)
  --   e≡e' = refl
  --   d≡e : d ≡ e
  --   d≡e =
  --     subst (Fin ∘ suc) (sym (+-suc l n))
  --            (subst (Fin ∘ suc) (+-suc l n) (fshift (suc l) c))
  --       ≡⟨ subst⁻Subst (Fin ∘ suc) q (fshift (suc l) c) ⟩
  --     fshift (suc l) c
  --       ≡⟨ refl ⟩
  --     fsuc (fshift l c) ▯ 
  --   h : Inj 0 (l + suc n)
  --   h = subst2 Inj refl (sym (+-suc l n)) (shift' (suc l) (nul _))
  --   h≡nul : h ≡ nul (l + suc n)
  --   h≡nul = 
  --     subst2 Inj refl (sym (+-suc l n)) (shift' (suc l) (nul _))
  --         ≡⟨ refl ⟩
  --     subst2 Inj refl (sym (+-suc l n)) (nul _)
  --       ≡⟨ sym (resubst (Inj 0) nul (sym (+-suc l n))) ⟩
  --     nul (l + suc n) ▯

{-

-- subst2 Inj refl (sym (+-suc l n))
--                    (subst2 Inj refl (sym (+-suc (suc l) n)) $ inc (subst Fin ? (fshift l b)) (shift' l g))

apply-inv≡nothing {suc l} {suc m} {n} b c g =
  apply-inv (shift (suc l) (inc c g)) (subst Fin (sym (+-suc (suc l) n)) f0)
    ≡⟨ refl ⟩
  apply-inv (shift (suc l) (inc c g)) (subst (Fin ∘ suc) (sym (+-suc l n)) f0)
    ≡⟨ cong (apply-inv (shift (suc l) (inc c g)))
            (sym (fzero≡subst-fzero (sym (+-suc l n)))) ⟩
  apply-inv (shift (suc l) (inc c g)) f0
    ≡⟨ cong (λ ○ → apply-inv ○ f0)
            (shift≡shift' (suc l) (inc c g))  ⟩
  apply-inv (shift' (suc l) (inc c g)) f0
    ≡⟨ refl ⟩
  apply-inv (subst2 Inj refl (sym (+-suc (suc l) n)) (inc d h)) f0
    ≡⟨ {!!} ⟩
  apply-inv (subst2 Inj refl (sym (+-suc (suc l) n)) (inc d h)) f0
    ≡⟨ {!!} ⟩
  nothing ▯
  where
    d : {!!}
    d = subst Fin (+-suc (suc l) n) (fshift (suc l) c)
    h : {!!}
    h = shift' (suc l) g

                   
apply-inv-⊕
  : {k l m n : ℕ} → (b : Fin (suc l)) (f : Inj k l) (g : Inj m n)
  → apply-inv (inc (finject n b) (f ⊕ g)) fzero
  ≡ map-Maybe (finject m) (apply-inv (inc b f) fzero)
apply-inv-⊕ {k = zero} {l = l} fzero f (nul _) = refl
apply-inv-⊕ {k = zero} {l = l} {m = zero} {n = n} (fsuc b) (nul _) (nul _) =
  apply-inv (inc (fsuc (finject n b)) (nul _ ⊕ nul n)) f0
    ≡⟨ cong (λ ○ → apply-inv (inc (fsuc (finject n b)) ○) f0) nul-⊕-nul ⟩
  apply-inv (inc (fsuc (finject n b)) (nul _)) f0
    ≡⟨ refl ⟩
  nothing ▯

  where
    p : {l : ℕ} (b : Fin (suc l))
      → fjoin (fsuc (finject n b)) f0 fzero≉fsuc
      ≡ finject n (fjoin (fsuc b) f0 fzero≉fsuc)
    p {l} b = refl
apply-inv-⊕ {k = zero} {l = l} {suc m} {suc n} fzero (nul l) (inc c g) = refl
apply-inv-⊕ {k = zero} {l = l} {suc m} {suc n} (fsuc b) (nul l) (inc c g) =
  apply-inv (inc (fsuc (finject (suc n) b)) (shift l (inc c g))) f0
    ≡⟨ refl ⟩
  apply-inv-rec (shift l (inc c g)) (fsuc (finject (suc n) b)) f0 (no fzero≉fsuc)
    ≡⟨ {!!} ⟩
  map-Maybe fsuc
   (apply-inv (nul l ⊕ inc c g)
              (fjoin f0 (fsuc (fin-restrict-< {b = fsuc (finject (suc n) b)} f0 <fzero)) fsuc≉fzero))
    ≡⟨ cong
        (λ ○ →
           map-Maybe fsuc
           (apply-inv (nul l ⊕ inc c g) (fjoin f0 (fsuc ○) fsuc≉fzero))) r ⟩
  map-Maybe fsuc
   (apply-inv (nul l ⊕ inc c g)
              (fjoin f0 (fsuc (subst Fin (sym (+-suc l n)) f0)) fsuc≉fzero))
    ≡⟨ cong (map-Maybe fsuc ∘ apply-inv (nul l ⊕ inc c g)) s ⟩
  map-Maybe fsuc
   (apply-inv (nul l ⊕ inc c g)
              (subst Fin (sym (+-suc l n)) f0))
    ≡⟨ cong (map-Maybe fsuc) {!!} ⟩
  map-Maybe fsuc nothing
    ≡⟨ refl ⟩
  nothing
    ≡⟨ refl ⟩
  map-Maybe (finject (suc m)) (map-Maybe fsuc nothing)
    ≡⟨ refl ⟩
  map-Maybe (finject (suc m)) (apply-inv-rec (nul l) (fsuc b) f0 (no fzero≉fsuc))
    ≡⟨ refl ⟩
  map-Maybe (finject (suc m)) (apply-inv (inc (fsuc b) (nul l)) f0) ▯
  where
    r : fin-restrict-< f0 <fzero
      ≡ subst Fin (sym (+-suc l n)) f0
    r = fin-restrict≡subst (fsuc (finject (suc n) b)) (fzero {l + n}) <fzero (sym (+-suc l n))
    s : fjoin f0 (fsuc (subst Fin (sym (+-suc l n)) f0)) fsuc≉fzero
      ≡ subst Fin (sym (+-suc l n)) f0
    s =
      fjoin f0 (fsuc (subst Fin (sym (+-suc l n)) f0)) fsuc≉fzero
        ≡⟨ refl ⟩
      subst Fin (sym (+-suc l n)) f0 ▯
 
apply-inv-⊕ {k = suc k} {l = l} {m} {n} b f g = {!!}


-- superposing
--   : {l m n : ℕ} (k : ℕ) (f : Inj (k + m) (k + n))
--   → trace k (α⁻¹ (f ⊕ idInj l))
--   ≡ trace k f ⊕ idInj l
-- superposing zero f = refl
-- superposing {l = l} (suc k) f =
--   trace k (pred (α⁻¹ (f ⊕ idInj l)))
--     ≡⟨ {!!} ⟩
--   trace k (pred f) ⊕ idInj l ▯

-- -}
