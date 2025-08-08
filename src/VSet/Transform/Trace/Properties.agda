module VSet.Transform.Trace.Properties where

open import VSet.Prelude
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base renaming (pred to fpred)
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Data.Maybe
open import VSet.Transform.Elementary.Base 
open import VSet.Transform.Inverse.Base 
open import VSet.Transform.Inverse.Insert
open import VSet.Transform.Inverse.Properties
open import VSet.Transform.Trace.Base
open import VSet.Transform.Tensor.Base
open import VSet.Transform.Compose.Base

private
  variable
    k k' l l' m m' n n' : ℕ

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
f0≡0→remove0≡pred (inc (fsuc b) f) f'0≡0 = absurd (fsuc≢fzero b f'0≡0)

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
    w : fjoin (fsuc b) f0 fzero≉fsuc ≡ {!!}
    w = {!!}
    -- v : apply-inv f f0 
    --   ≡ nothing
    -- v = mapMaybeNothing f⁻¹0≡∅


thm1-2-1-pred
  : (f : Inj (suc m) (suc n)) (g : Inj l m)
  → pred (f ∘ʲ (𝟙 {1} ⊕ g)) ≡ (pred f) ∘ʲ g
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
--          → trace k (f ∘ʲ ((𝟙 {k}) ⊕ g)) ≡ (trace k f) ∘ʲ g
-- thm1-2-1 {zero} {l} {m} {n} f (nul l) = {!!}
-- -- thm1-2-1 {suc zero} {l} {m} {n} f (nul l) = refl
-- thm1-2-1 {suc k} {l} {suc m} {n} f (nul l) with apply f f0
-- ... | fzero =
--   trace k (pred (inc f0 (remove f0 f ∘ʲ (𝟙 ⊕ (nul l)))))
--     ≡⟨ cong (trace k) (pred-0 (remove f0 f ∘ʲ (𝟙 ⊕ (nul l)))) ⟩
--   trace k (remove f0 f ∘ʲ (𝟙 ⊕ (nul l)))
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

open import Cubical.Data.Nat.Properties

Thm1-2-2-Pred : ∀ {l m n} (f : Inj m n) (g : Inj (suc l) (suc m)) → Type
Thm1-2-2-Pred {l} {m} {n} f g = (f' ∘ʲ g) —1 ≡ f ∘ʲ (g —1)
  where
    f' : Inj (suc m) (suc n)
    f' = subst2 Inj (+-comm m 1) (+-comm n 1) (f ⊕ 𝟙)

  -- inc (apply g b) (remove b g ∘ʲ f)

thm1-2-2-pred : ∀ {l m n} (f : Inj m n) (g : Inj (suc l) (suc m))
              → Thm1-2-2-Pred f g
thm1-2-2-pred {zero} {zero} {n} (nul _) (inc fzero (nul _)) = refl
thm1-2-2-pred {l} {suc m} {suc n} (inc b f) (inc fzero g) with b
... | b =
  (f' ∘ʲ inc fzero g) —1
    ≡⟨ refl ⟩
  (inc (apply f' fzero) (remove fzero f' ∘ʲ g)) —1
    ≡⟨ {!!} ⟩
  inc b f ∘ʲ g
    ≡⟨ cong (inc b f ∘ʲ_) (sym (pred-0 g) ) ⟩
  inc b f ∘ʲ (inc fzero g —1) ▯
  where
    f' : Inj (suc (suc m)) (suc (suc n))
    f' = subst2 Inj (+-comm (suc m) 1) (+-comm (suc n) 1) ((inc b f) ⊕ 𝟙)
    u : f' ≡ inc (finj b) (subst2 Inj (+-comm m 1) (+-comm n 1) (f ⊕ 𝟙))
    u =
      subst2 Inj (+-comm (suc m) 1) (+-comm (suc n) 1) ((inc b f) ⊕ 𝟙)
        ≡⟨ refl  ⟩
      subst2 Inj (+-comm (suc m) 1) (+-comm (suc n) 1) (inc (finject 1 b) (f ⊕ 𝟙))
        ≡⟨ sym (subst2-inc-reorder (+-comm m 1) (+-comm n 1) (finject 1 b) (f ⊕ 𝟙)) ⟩
      inc (subst (Fin ∘ suc) (+-comm n 1) (finject 1 b))
          (subst2 Inj (+-comm m 1) (+-comm n 1) (tensor f 𝟙))
        ≡⟨ {!!} ⟩
      inc (finj b)
          (subst2 Inj (+-comm m 1) (+-comm n 1) (tensor f 𝟙))
        ≡⟨ {!!} ⟩
      inc (finj b) (subst2 Inj (+-comm m 1) (+-comm n 1) (tensor f 𝟙)) ▯
thm1-2-2-pred {l} {suc m} {suc n} (inc b f) (inc (fsuc c) g) = {!!}
  -- (f' ∘ʲ (inc c g)) —1
  --   ≡⟨ refl ⟩
  -- (inc (apply f' c) (remove c f' ∘ʲ g)) —1
  --   ≡⟨ {!!} ⟩
  -- (inc (apply f' c) (remove c f' ∘ʲ g)) —1
  --   ≡⟨ {!!} ⟩
  -- (inc b f ∘ʲ (inc c g —1)) ▯
  -- where
  --   f' : Inj (suc m) (suc n)
  --   f' = subst2 Inj (+-comm m 1) (+-comm n 1) ((inc b f) ⊕ 𝟙)
