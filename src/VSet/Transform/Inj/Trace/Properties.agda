module VSet.Transform.Inj.Trace.Properties where

open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Properties
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base renaming (pred to fpred)
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Data.Maybe
open import VSet.Data.Nat.Properties
open import VSet.Prelude
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Elementary.Base 
open import VSet.Transform.Inj.Inverse.Base 
open import VSet.Transform.Inj.Inverse.Insert
open import VSet.Transform.Inj.Inverse.Properties
open import VSet.Transform.Inj.Tensor.Associator 
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties
open import VSet.Transform.Inj.Trace.Base

private
  variable
    k k' l l' m m' n n' : ℕ
    A B C D U V W X Y Z : ℕ

pred-0 : (f : Inj m n)
       → pred (inc f0 f) ≡ f
pred-0 {zero} (nul _) = refl
pred-0 {suc m} {suc n} f = refl

remove-insert
  : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
  → (f : Inj m n)
  → remove a (insert a b f) ≡ f
remove-insert fzero b (nul _) = refl
remove-insert fzero b (inc c f) = refl
remove-insert (fsuc fzero) b (inc c f) =
  remove (fsuc fzero) (insert (fsuc fzero) b (inc c f))
    ≡⟨ refl ⟩
  remove (fsuc fzero) (inc (fsplice b c) (insert fzero (fcross c b) f))
    ≡⟨ refl ⟩
  remove (fsuc fzero) (inc (fsplice b c) (inc (fcross c b) f))
    ≡⟨ refl ⟩
  inc (fcross (apply (inc (fcross c b) f) fzero) (fsplice b c))
      (remove fzero (inc (fcross c b) f)) 
    ≡⟨ refl ⟩
  inc (fcross (apply (inc (fcross c b) f) fzero) (fsplice b c)) f 
    ≡⟨ refl ⟩
  inc (fcross (fcross c b) (fsplice b c)) f 
    ≡⟨ cong (λ ○ → inc ○ f) (fcross-fcross-fsplice b c) ⟩
  inc c f ▯
remove-insert {m = suc m} {n = suc n} (fsuc a) b (inc c f) =
  let b' : Fin (suc n)
      b' = apply (insert a (fcross c b) f) a
  in
  remove (fsuc a) (insert (fsuc a) b (inc c f))
    ≡⟨ refl ⟩
  remove (fsuc a) (inc (fsplice b c) (insert a (fcross c b) f))
    ≡⟨ refl ⟩
  inc (fcross (apply (insert a (fcross c b) f) a) (fsplice b c))
      (remove a (insert a (fcross c b) f)) 
    ≡⟨ refl ⟩
  inc (fcross b' (fsplice b c))
      (remove a (insert a (fcross c b) f))
    ≡⟨ cong₂ inc (sym (fjoin-fsplice-fsplice-fsplice b b' c
                        (≉fsym (fsplice≉b (fsplice b c) b')))) refl ⟩
  inc (fjoin (fsplice (fsplice b c) b') (fsplice b c)
                 (≉fsym (fsplice≉b (fsplice b c) b')))
      (remove a (insert a (fcross c b) f))
    ≡⟨ cong (inc _) (remove-insert a (fcross c b) f) ⟩
  inc (fjoin (fsplice (fsplice b c) b') (fsplice b c)
                 (≉fsym (fsplice≉b (fsplice b c) b'))) f
    ≡⟨ cong (λ ○ → inc ○ f) (fjoin-fsplice-fsplice-fsplice b b' c _) ⟩
  inc (fcross b' (fsplice b c)) f 
    ≡⟨ cong (λ ○ → inc (fcross ○ (fsplice b c)) f) (apply-insert≡b a (fcross c b) f) ⟩
  inc (fcross (fcross c b) (fsplice b c)) f 
    ≡⟨ cong (λ ○ → inc ○ f) (fcross-fcross-fsplice b c) ⟩
  inc c f ▯

tensor-trace-inverse : (l : ℕ) {m n : ℕ} → (f : Inj m n) → trace l ((idInj l) ⊕ f) ≡ f
tensor-trace-inverse zero f = refl
tensor-trace-inverse (suc l) {m} {n} f =
  trace (suc l) (idInj (suc l) ⊕ f)
    ≡⟨ refl ⟩
  trace (suc l) (inc fzero (idInj l) ⊕ f)
    ≡⟨ refl ⟩
  trace l (pred (inc fzero (idInj l) ⊕ f))
    ≡⟨ refl ⟩
  trace l (pred (inc (finject n fzero) ((idInj l) ⊕ f)))
    ≡⟨ refl ⟩
  trace l (pred (inc fzero ((idInj l) ⊕ f)))
    ≡⟨ cong (trace l) (pred-0 (idInj l ⊕ f)) ⟩
  trace l ((idInj l) ⊕ f)
    ≡⟨ tensor-trace-inverse l f ⟩
  f ▯

f0≡0→remove0≡pred
  : (f : Inj (suc m) (suc n))
  → apply f f0 ≡ f0
  → remove f0 f ≡ pred f
f0≡0→remove0≡pred (inc fzero f) f'0≡0 = sym (pred-0 f)
f0≡0→remove0≡pred (inc (fsuc b) f) f'0≡0 = absurd (fsuc≢fzero f'0≡0)

f⁻¹0≡∅→remove0≡pred 
  : (f : Inj (suc m) (suc n)) (c : Fin n)
  → apply f f0 ≡ fsuc c
  → apply-inv f f0 ≡ nothing
  → remove f0 f ≡ pred f
f⁻¹0≡∅→remove0≡pred {m = zero} (inc b (nul _)) c 0≡c' f⁻¹0≡∅ = refl
f⁻¹0≡∅→remove0≡pred {m = suc m} (inc fzero f) c 0≡c' f⁻¹0≡∅ = {!!}
f⁻¹0≡∅→remove0≡pred {m = suc m} {n = suc n} (inc (fsuc b) f) c 0≡c' f⁻¹0≡∅ = 
  remove f0 (inc (fsuc b) f)
    ≡⟨ refl ⟩
  f
    ≡⟨ {!!} ⟩
  pred (inc (fsuc b) f) ▯
  where
    u : apply-inv f (fjoin (fsuc b) f0 fzero≉fsuc)
      ≡ nothing
    u = mapMaybeNothing f⁻¹0≡∅
    w : fjoin (fsuc b) f0 fzero≉fsuc ≡ b
    w = {!!}
    -- v : apply-inv f f0 
    --   ≡ nothing
    -- v = mapMaybeNothing f⁻¹0≡∅




thm1-2-1-pred
  : (f : Inj (suc m) (suc n)) (g : Inj l m)
  → pred (f ∘ʲ (Id {1} ⊕ g)) ≡ (pred f) ∘ʲ g
thm1-2-1-pred f (nul _) = refl
thm1-2-1-pred {m = m} {n = zero} (inc _ ()) (inc b g)
thm1-2-1-pred {m = m} {n = suc n} f (inc b g) with inspect' (apply f f0)
... | fzero , f0≡0 =
  pred (inc (apply f f0) (remove f0 f ∘ʲ inc b g))
    ≡⟨ cong (λ ○ → pred (inc ○ (remove f0 f ∘ʲ inc b g))) f0≡0 ⟩
  pred (inc f0 (remove f0 f ∘ʲ inc b g))
    ≡⟨ refl ⟩
  remove f0 f ∘ʲ inc b g
    ≡⟨ cong (_∘ʲ inc b g) (f0≡0→remove0≡pred f f0≡0) ⟩
  pred f ∘ʲ inc b g ▯
... | fsuc c , f0≡c' =
  pred (inc (apply f f0) (remove f0 f ∘ʲ inc b g))
    ≡⟨ refl ⟩
  pred (inc (apply f f0) (inc (apply (remove f0 f) b) (remove b (remove f0 f) ∘ʲ g)))
    ≡⟨ cong (λ ○ → pred (inc ○ (inc (apply (remove f0 f) b)
                                    (remove b (remove f0 f) ∘ʲ g))))
           f0≡c' ⟩
  pred (inc (fsuc c) (inc (apply (remove f0 f) b) (remove b (remove f0 f) ∘ʲ g)))
    ≡⟨ {!!} ⟩
  pred f ∘ʲ inc b g ▯
  where
    h = (inc (apply (remove f0 f) b) (remove b (remove f0 f) ∘ʲ g))
    w : remove f0 f ≡ pred f
    w = {!!}
    -- u : pred-cases c h (apply-inv (inc (fsuc c) h) f0)
    --   ≡ pred f ∘ʲ inc b g
    -- u with inspect' (apply-inv (inc (fsuc c) h) f0)
    -- u | nothing , p =
    --   pred-cases c h (apply-inv (inc (fsuc c) h) f0)
    --     ≡⟨ cong (pred-cases c h) p ⟩
    --   pred-cases c h nothing
    --     ≡⟨ refl ⟩
    --   inc (apply (remove f0 f) b) (remove b (remove f0 f) ∘ʲ g)
    --     ≡⟨ {!!} ⟩
    --   inc (apply (pred f) b) (remove b (pred f) ∘ʲ g)
    --     ≡⟨ refl ⟩
    --   pred f ∘ʲ inc b g ▯
    -- u | just a' , p = {!!}
-- thm1-2-1 : (f : Inj (k + m) (k + n)) (g : Inj l m)
--          → trace k (f ∘ʲ ((Id {k}) ⊕ g)) ≡ (trace k f) ∘ʲ g
-- thm1-2-1 {zero} {l} {m} {n} f (nul l) = {!!}
-- -- thm1-2-1 {suc zero} {l} {m} {n} f (nul l) = refl
-- thm1-2-1 {suc k} {l} {suc m} {n} f (nul l) with apply f f0
-- ... | fzero =
--   trace k (pred (inc f0 (remove f0 f ∘ʲ (Id ⊕ (nul l)))))
--     ≡⟨ cong (trace k) (pred-0 (remove f0 f ∘ʲ (Id ⊕ (nul l)))) ⟩
--   trace k (remove f0 f ∘ʲ (Id ⊕ (nul l)))
--     ≡⟨ thm1-2-1 (remove f0 f) (nul l) ⟩
--   nul (suc m) ▯
-- ... | fsuc b =
--   trace k
--    (pred (inc (fsuc b) (remove f0 f ∘ʲ tensor (idInj k) (nul l))))
--     ≡⟨ {!!} ⟩
--   trace k
--    (pred-cases b (remove f0 f ∘ʲ tensor (idInj k) (nul l))
--      apply-inv (inc (fsuc b) (remove f0 f ∘ʲ tensor (idInj k) (nul l))) f0)
--     ≡⟨ {!!} ⟩
--   nul m ▯
-- thm1-2-1 f (inc b g) = {!!}

Thm1-2-2-Pred : ∀ {l m n} (f : Inj m n) (g : Inj (suc l) (suc m)) → Type
Thm1-2-2-Pred f g = ((f ⊕⁻ Id) ∘ʲ g) —1 ≡ f ∘ʲ (g —1)

thm1-2-3 : ∀ {A B X Y} (f : Inj (X +⁻ A) (Y +⁻ B)) (g : Inj B A)
         → ((Id {Y} ⊕⁻ g) ∘ʲ f) — A ≡ (f ∘ʲ (Id {X} ⊕⁻ g)) — B
thm1-2-3 {A} {B} {X} {Y} f g = {!!}

thm1-2-4 : (f : Inj (X +⁻ 0) (Y +⁻ 0)) → f — 0 ≡ f
thm1-2-4 f = refl

subst-pred-reorder : ∀ {m m' n n'} (p : m ≡ m') (q : n ≡ n') (f : Inj (suc m) (suc n))
                   → subst2 Inj p q (f —1)
                   ≡ subst2 Inj (cong suc p) (cong suc q) f —1
subst-pred-reorder p q f =
  subst2-reorder' Injsuc Inj (λ g → g —1) p q f

pred-α⁻¹-reorder : {k l m n : ℕ} (f : Inj (((suc m) + n) + l) (((suc m) + n) + k))
                 → pred (α⁻¹ f) ≡ α⁻¹ (pred f)
pred-α⁻¹-reorder (inc b f) = refl

vanishing₁ : {f : Inj m n} → trace 0 (nul 0 ⊕ f) ≡ f
vanishing₁ = refl

vanishing₂ : {k l m n : ℕ} → (f : Inj ((m + n) + k) ((m + n) + l))
           → trace n (trace m (α⁻¹ f))
           ≡ trace (m + n) f
vanishing₂ {m = zero} f = refl
vanishing₂ {m = suc m} {n = n} f =
  trace n (trace m (pred (α⁻¹ f)))
    ≡⟨ cong (trace n ∘ trace m) (pred-α⁻¹-reorder f) ⟩
  trace n (trace m (α⁻¹ (pred  f)))
    ≡⟨ vanishing₂ (pred f) ⟩
  trace (m + n) (pred f)
    ≡⟨ refl ⟩
  trace (suc m + n) f ▯

-- superposing-pred
--   : {m n : ℕ} (l : ℕ) (f : Inj (suc m) (suc n))
--   → pred (f ⊕ idInj l)
--   ≡ pred f ⊕ idInj l
-- superposing-pred {m = 0} l (inc b (nul n)) =
--   pred (inc b (nul n) ⊕ idInj l)
--     ≡⟨ refl ⟩
--   pred (inc (finject l b) (tensor (nul n) (idInj l)))
--     ≡⟨ cong pred (cong₂ inc (sym (substSubst⁻ (Fin ∘ suc) (+-zero (n + l)) (finject l b)))
--                  (sym (transportTransport⁻ (cong₂ Inj (+-zero (0 + l)) (+-zero (n + l))) (nul n ⊕ idInj l)))) ⟩
--   pred (inc (subst (Fin ∘ suc) (+-zero (n + l))
--              (subst (Fin ∘ suc) (sym (+-zero (n + l)))
--               (finject l b)))
--             (subst2 Inj (+-zero (0 + l)) (+-zero (n + l))
--              (subst2 Inj (sym (+-zero (0 + l))) (sym (+-zero (n + l)))
--               (nul n ⊕ idInj l))))
--     ≡⟨ cong pred (sym (subst2-inc-reorder (+-zero (0 + l)) (+-zero (n + l))
--                                           (subst (Fin ∘ suc) (sym (+-zero (n + l))) (finject l b))
--                                           (subst2 Inj (sym (+-zero (0 + l))) (sym (+-zero (n + l))) (tensor (nul n) (idInj l))))) ⟩
--   pred (subst2 Injsuc (+-zero (0 + l)) (+-zero (n + l))
--                (inc (subst (Fin ∘ suc) (sym (+-zero (n + l))) (finject l b))
--                     ((subst2 Inj (sym (+-zero (0 + l))) (sym (+-zero (n + l)))
--                              (nul n ⊕ idInj l)))))
--     ≡⟨ {!cong pred!} ⟩
--   (nul n) ⊕ (idInj l)
--     ≡⟨ {!!} ⟩
--   pred (inc b (nul n)) ⊕ idInj l ▯
-- superposing-pred zero (inc fzero f) =
--   pred (inc fzero f ⊕ nul 0)
--     ≡⟨ refl ⟩
--   pred (inc fzero (f ⊕ nul 0))
--     ≡⟨ {!!} ⟩
--   f ⊕ nul 0
--     ≡⟨ {!!} ⟩
--   pred (inc fzero f) ⊕ nul 0 ▯
-- superposing-pred zero (inc b f) =
--   pred (inc b f ⊕ nul 0)
--     ≡⟨ refl ⟩
--   pred (inc (finject 0 b) (f ⊕ nul 0))
--     ≡⟨ {!!} ⟩
--   pred (inc b f) ⊕ nul 0 ▯
-- superposing-pred (suc l) f = {!!}

pred-inc0 : {m n : ℕ} → (f : Inj m n)
  → pred (inc fzero f) ≡ f
pred-inc0 {zero} {n} (nul _) = refl
pred-inc0 {suc m} {suc n} (inc b f) = refl

pred-inc-nul : {n : ℕ} → (b : Fin (suc n))
  → pred (inc b (nul _)) ≡ nul _
pred-inc-nul {n} b = refl

superposing-pred
  : {m n : ℕ} (l : ℕ) (f : Inj (suc m) (suc n))
  → pred (f ⊕ idInj l)
  ≡ pred f ⊕ idInj l
superposing-pred {m = 0} l (inc fzero (nul n)) =
  pred (inc fzero (nul n) ⊕ idInj l)
    ≡⟨ refl ⟩
  pred (inc fzero (nul n ⊕ idInj l))
    ≡⟨ pred-inc0 (nul n ⊕ idInj l) ⟩
  nul n ⊕ idInj l
    ≡⟨ refl ⟩
  pred (inc fzero (nul n)) ⊕ idInj l ▯
superposing-pred {m = zero} {n = n} zero (inc (fsuc b) (nul _)) =
  pred (inc (fsuc b) (nul _) ⊕ idInj zero)
    ≡⟨ refl ⟩
  pred (inc (fsuc (finject zero b)) (nul _ ⊕ nul 0))
    ≡⟨ refl ⟩
  pred (inc (fsuc (finject zero b)) (shift _ (nul 0)))
    ≡⟨ shift-nul 0 n ⟩
  pred (inc (fsuc (finject zero b)) (nul (n + 0)))
    ≡⟨ refl ⟩
  nul (n + 0)
    ≡⟨ sym (shift-nul 0 n) ⟩
  shift _ (nul 0)
    ≡⟨ refl ⟩
  pred (inc (fsuc b) (nul _)) ⊕ nul 0 ▯
superposing-pred {m = zero} {n = zero} (suc l) (inc (fsuc b) (nul _)) =
  pred (inc (fsuc b) (nul _) ⊕ idInj (suc l))
    ≡⟨ refl ⟩
  pred (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l)))
    ≡⟨ refl ⟩
  pred {m = suc l} {n = suc l} (inc (fsuc (finject (suc l) b)) (shift _ (idInj (suc l))))
    ≡⟨ refl ⟩
  pred-cases (shift _ (idInj (suc l))) (apply-inv (inc (fsuc (finject (suc l) b)) (shift _ (idInj (suc l)))) fzero) (finject (suc l) b)
    ≡⟨ cases ⟩
  shift _ (idInj (suc l))
    ≡⟨ refl ⟩
  pred (inc (fsuc b) (nul _)) ⊕ idInj (suc l) ▯
  where
    cases : pred-cases (shift _ (idInj (suc l))) (apply-inv (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l))) fzero) (finject (suc l) b)
          ≡ shift _ (idInj (suc l))
    cases = case (apply-inv (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l))) fzero) of
      λ{ nothing → refl
       ; (just fzero) → refl
       ; (just (fsuc a)) → refl
       }
superposing-pred {m = zero} {n = (suc n)} (suc l) (inc (fsuc b) (nul _)) =
  pred (inc (fsuc b) (nul _) ⊕ idInj (suc l))
    ≡⟨ refl ⟩
  pred (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l)))
    ≡⟨ refl ⟩
  pred-cases (shift _ (idInj (suc l))) (apply-inv (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l))) fzero) (finject (suc l) b)
    ≡⟨ cases ⟩
  shift _ (idInj (suc l))
    ≡⟨ refl ⟩
  pred (inc (fsuc b) (nul _)) ⊕ idInj (suc l) ▯
  where
    cases : pred-cases (shift _ (idInj (suc l))) (apply-inv (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l))) fzero) (finject (suc l) b)
          ≡ shift _ (idInj (suc l))
    cases = case (apply-inv (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l))) fzero) of
      λ{ nothing → refl
       ; (just fzero) → refl
       ; (just (fsuc a)) → refl
       }
superposing-pred {m = suc m} {n = suc n} l (inc fzero f) = refl
superposing-pred {m = suc m} {n = suc n} l (inc (fsuc b) f) =
  pred (inc (fsuc b) f ⊕ idInj l)
    ≡⟨ refl ⟩
  pred (inc (fsuc (finject l b)) (f ⊕ idInj l))
    ≡⟨ refl ⟩
  pred-cases (f ⊕ idInj l) (apply-inv (inc (fsuc (finject l b)) (f ⊕ idInj l)) fzero) (finject l b)
    ≡⟨ {!cases!} ⟩
  pred-cases f (apply-inv (inc (fsuc b) f) fzero) b ⊕ idInj l
    ≡⟨ refl ⟩
  pred (inc (fsuc b) f) ⊕ idInj l ▯
  where
    cases : pred-cases (shift _ (idInj (suc l)))
                       (apply-inv (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l)))
                                  fzero) (finject (suc l) b)
          ≡ shift _ (idInj (suc l))
    cases = case (apply-inv (inc (fsuc (finject (suc l) b)) (nul _ ⊕ idInj (suc l))) fzero) of
      λ{ nothing → refl
       ; (just fzero) → refl
       ; (just (fsuc a)) → refl
       }

-- apply-inv-⊕
--   : {k l m n : ℕ} → (b : Fin (suc l)) (f : Inj k l) (g : Inj m n)
--   → apply-inv (inc (finject n b) (f ⊕ g)) fzero
--   ≡ map-Maybe (finject m) (apply-inv (inc b f) fzero)
-- apply-inv-⊕ {m = m} {n = n} fzero f g = refl
-- apply-inv-⊕ {m = zero} {n = n} (fsuc b) f (nul n) with apply-inv (inc (fsuc b) f) fzero
-- ... | nothing = {!!}
-- ... | just x = {!!}
--   -- apply-inv (inc (finject n (fsuc b)) (f ⊕ nul n)) fzero
--   --   ≡⟨ {!!} ⟩
--   -- map-Maybe (finject 0) x ▯
-- apply-inv-⊕ {m = suc m} {n = suc n} (fsuc b) f (inc c g) = {!!}
--   -- apply-inv (inc (finject n b) (f ⊕ g)) fzero
--   --   ≡⟨ {!!} ⟩
--   -- map-Maybe (finject m) (apply-inv (inc b f) fzero) ▯

cong-suc-predℕ : {l m : ℕ} (p : suc m ≡ suc l)
           → cong (Fin ∘ suc ∘ predℕ) p ≡ cong Fin p
cong-suc-predℕ {l = l} {m = m} p =
  transport (λ i → (λ j → suc-predℕ (p j) (pi≢0 j) i)
                 ≡ (λ i → p i)) refl
  where
    q : ∀ (x : ℕ) (x≢0 : x ≢ 0) → suc (predℕ x) ≡ x
    q x x≢0 = sym (suc-predℕ x x≢0)
    p0≡pi : ∀ i → p i0 ≡ p i
    p0≡pi i = λ j → p (i ∧ j)
    pi≢0 : ∀ i → p i ≢ 0
    pi≢0 i = subst (_≢ 0) (p0≡pi i) snotz

fin-restrict≡subst
  : {l m : ℕ} (b : Fin (suc l)) (a : Fin m) → (a<b : a <ᶠ b) → (p : m ≡ l)
  → fin-restrict-< a a<b ≡ subst Fin p a
fin-restrict≡subst {l = zero} {m = suc m} b a a<b p = absurd (snotz p)
fin-restrict≡subst {l = suc l} {m = suc m} (fsuc b) fzero <fzero p =
  fin-restrict-< f0 <fzero
    ≡⟨ refl ⟩
  fzero {l}
    ≡⟨ fzero≡subst-fzero (cong predℕ p) ⟩
  subst (Fin ∘ suc ∘ predℕ) p (fzero {m})
    ≡⟨ cong (λ ○ → transport ○ (fzero {m})) (cong-suc-predℕ p) ⟩
  subst Fin p (fzero {m}) ▯
fin-restrict≡subst {l = zero} {m = zero} fzero () () p
fin-restrict≡subst {l = zero} {m = zero} (fsuc b) () a<b p
fin-restrict≡subst {l = suc l} {m = suc m} (fsuc b) (fsuc a) (<fsuc a<b) p =
  fin-restrict-< (fsuc a) (<fsuc a<b)
    ≡⟨ refl ⟩
  fsuc (fin-restrict-< a a<b) 
    ≡⟨ cong fsuc (fin-restrict≡subst b a a<b (injSuc p)) ⟩
  fsuc (subst Fin (injSuc p) a)
    ≡⟨ sym (subst-fsuc-reorder (cong predℕ p) a) ⟩
  subst (Fin ∘ suc ∘ predℕ) p (fsuc a)
    ≡⟨ cong (λ ○ → transport ○ (fsuc a)) (cong-suc-predℕ p)  ⟩
  subst Fin p (fsuc a) ▯

