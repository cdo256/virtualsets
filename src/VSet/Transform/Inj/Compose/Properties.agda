module VSet.Transform.Inj.Compose.Properties where

open import VSet.Prelude
open import Cubical.Data.Prod.Base hiding (map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import Cubical.Data.List.Base hiding ([_])
open import VSet.Data.Inj.Base
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Elementary.Base

applyId : ∀ {m : ℕ} (a : Fin m) → apply (idInj m) a ≡ a
applyId fzero = refl
applyId (fsuc a) = cong fsuc (applyId a)

-- fcross-fsplice-remove-splice-fcross-fcross-fsplice
--   : {m n : ℕ}
--   → (b : Fin (suc m)) (c : Fin m) (d : Fin (suc (suc n))) (e : Fin (suc (suc n)))
--   → (g : Inj (suc m) (suc n))
--   → fcross
--       (fsplice (fcross (apply g (fsplice b c)) e)
--                (apply (remove (fsplice b c) g) (fcross c b)))
--       (fcross (fsplice e (apply g (fsplice b c))) (fsuc d))
--     ≡
--     fcross
--       (fsplice (fcross (apply g b) e) (apply (remove b g) c))
--       (fcross (fsplice e (apply g b)) (fsuc d))
-- fcross-fsplice-remove-splice-fcross-fcross-fsplice {m = suc m} {n = suc n} fzero fzero fzero e (inc a (inc a' g)) =
--   fcross (fsplice (fcross (apply (inc a (inc a' g)) (fsplice f0 f0)) e)
--                   (apply (remove (fsplice f0 f0) (inc a (inc a' g))) (fcross f0 f0)))
--    (fcross (fsplice e (apply (inc a (inc a' g)) (fsplice f0 f0))) f1)
--     ≡⟨ refl ⟩
--   fcross (fsplice (fcross (fsplice a a') e)
--                   (apply (remove f1 (inc a (inc a' g))) f0))
--          (fcross (fsplice e (apply (inc a (inc a' g)) f1)) f1)
--     ≡⟨ refl ⟩
--   fcross (fsplice (fcross (fsplice a a') e)
--                   (apply (inc (fcross (apply ? ?) ? (remove ? ?))) f0))
--          (fcross (fsplice e (fsplice a (apply (inc a' g) f0))) f1)
--     ≡⟨ {!!} ⟩
--   fcross (fsplice (fcross a e) (apply (inc a' g) f0)) (fcross (fsplice e a) f1)
--     ≡⟨ refl ⟩
--   fcross (fsplice (fcross (apply (inc a (inc a' g)) f0) e)
--                   (apply (remove f0 (inc a (inc a' g))) f0))
--          (fcross (fsplice e (apply (inc a (inc a' g)) f0)) f1) ▯
-- fcross-fsplice-remove-splice-fcross-fcross-fsplice fzero fzero (fsuc d) e g = {!!}
-- fcross-fsplice-remove-splice-fcross-fcross-fsplice fzero (fsuc c) d e g = {!!}
-- fcross-fsplice-remove-splice-fcross-fcross-fsplice (fsuc b) c d e g = {!!}

-- fcross-appply-remove-splice-fcross-fcross-apply-fsplice
--   : {m n : ℕ}
--   → (b : Fin (suc (suc m))) (c : Fin (suc m)) (d : Fin (suc (suc (suc n))))
--   → (g : Inj (suc (suc m)) (suc (suc n)))
--   → fcross (apply (remove (fsplice b c) g) (fcross c b))
--            (fcross (apply g (fsplice b c)) d)
--   ≡ fcross (apply (remove b g) c) (fcross (apply g b) d)
-- fcross-appply-remove-splice-fcross-fcross-apply-fsplice fzero fzero d (inc e1 (inc e2 g)) =
--   fcross (apply (remove (fsplice f0 f0) (inc e1 (inc e2 g))) (fcross f0 f0))
--    (fcross (apply (inc e1 (inc e2 g)) (fsplice f0 f0)) d) ≡⟨ refl ⟩
--   fcross (apply (remove f1 (inc e1 (inc e2 g))) f0)
--          (fcross (apply (inc e1 (inc e2 g)) f1) d)
--     ≡⟨ refl ⟩
--   fcross (apply (inc (fcross (apply (inc e2 g) f0) e1) (remove f0 (inc e2 g))) f0)
--          (fcross (fsplice e1 (apply (inc e2 g) f0)) d)
--     ≡⟨ refl ⟩
--   fcross (fcross e2 e1)
--          (fcross (fsplice e1 e2) d)
--     ≡⟨ fcross-fcross-fcross-fsplice d e1 e2 ⟩
--   fcross e2 (fcross e1 d)
--     ≡⟨ refl ⟩
--   fcross (apply (inc e2 g) f0) (fcross e1 d) ▯
-- fcross-appply-remove-splice-fcross-fcross-apply-fsplice b c fzero (inc e1 (inc e2 g)) =
--   fcross (apply (remove (fsplice b c) (inc e1 (inc e2 g))) (fcross c b))
--          (fcross (apply (inc e1 (inc e2 g)) (fsplice b c)) f0)
--     ≡⟨ cong (fcross
--    (apply (remove (fsplice b c) (inc e1 (inc e2 g))) (fcross c b)))
--           (fcross0≡0 (apply (inc e1 (inc e2 g)) (fsplice b c))) ⟩
--   fcross (apply (remove (fsplice b c) (inc e1 (inc e2 g))) (fcross c b)) f0
--     ≡⟨ fcross0≡0 (apply (remove (fsplice b c) (inc e1 (inc e2 g))) (fcross c b)) ⟩
--   f0
--     ≡⟨ sym (fcross0≡0 (apply (remove b (inc e1 (inc e2 g))) c)) ⟩
--   fcross (apply (remove b (inc e1 (inc e2 g))) c) f0
--     ≡⟨ cong (fcross (apply (remove b (inc e1 (inc e2 g))) c))
--             (sym (fcross0≡0 (apply (inc e1 (inc e2 g)) b))) ⟩
--   fcross (apply (remove b (inc e1 (inc e2 g))) c)
--    (fcross (apply (inc e1 (inc e2 g)) b) f0) ▯
-- fcross-appply-remove-splice-fcross-fcross-apply-fsplice fzero c d (inc e g) =
--   fcross (apply (remove (fsplice f0 c) (inc e g)) (fcross c f0))
--          (fcross (apply (inc e g) (fsplice f0 c)) d)
--     ≡⟨ cong (λ ○ → fcross (apply (remove (fsuc c) (inc e g)) ○)
--          (fcross (apply (inc e g) (fsuc c)) d)) (fcross0≡0 c) ⟩
--   fcross (apply (inc (fcross (apply g c) e) (remove c g)) f0)
--          (fcross (apply (inc e g) (fsuc c)) d)
--     ≡⟨ refl ⟩
--   fcross (fcross (apply g c) e)
--          (fcross (fsplice e (apply g c)) d)
--     ≡⟨ fcross-fcross-fcross-fsplice d e (apply g c) ⟩
--   fcross (apply g c)
--          (fcross e d)
--     ≡⟨ refl ⟩
--   fcross (apply (remove f0 (inc e g)) c)
--          (fcross (apply (inc e g) f0) d) ▯
-- fcross-appply-remove-splice-fcross-fcross-apply-fsplice (fsuc b) fzero (fsuc d) (inc e g) =
--   fcross (apply (remove (fsplice (fsuc b) f0) (inc e g))
--                 (fcross f0 (fsuc b)))
--          (fcross (apply (inc e g) (fsplice (fsuc b) f0)) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply g b)
--          (fcross e (fsuc d))
--     ≡⟨ sym (fcross-fcross-fcross-fsplice (fsuc d) e (apply g b)) ⟩
--   fcross (fcross (apply g b) e)
--          (fcross (fsplice e (apply g b)) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (inc (fcross (apply g b) e) (remove b g)) f0)
--          (fcross (fsplice e (apply g b)) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (remove (fsuc b) (inc e g)) f0)
--          (fcross (apply (inc e g) (fsuc b)) (fsuc d)) ▯
-- fcross-appply-remove-splice-fcross-fcross-apply-fsplice {suc m} {suc n} (fsuc b) (fsuc c) (fsuc d) (inc fzero g) =
--   fcross (apply (remove (fsplice (fsuc b) (fsuc c)) (inc fzero g)) (fcross (fsuc c) (fsuc b)))
--          (fcross (apply (inc fzero g) (fsplice (fsuc b) (fsuc c))) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (remove (fsuc (fsplice b c)) (inc fzero g)) (fsuc (fcross c b)))
--          (fcross (apply (inc fzero g) (fsuc (fsplice b c))) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (inc (fcross (apply g (fsplice b c)) fzero) (remove (fsplice b c) g))
--                 (fsuc (fcross c b)))
--          (fcross (fsuc (apply g (fsplice b c))) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (fsplice (fcross (apply g (fsplice b c)) fzero)
--                   (apply (remove (fsplice b c) g) (fcross c b)))
--          (fsuc (fcross (apply g (fsplice b c)) d))
--     ≡⟨ cong (λ ○ → fcross (fsplice ○ (apply (remove (fsplice b c) g) (fcross c b)))
--                           (fsuc (fcross (apply g (fsplice b c)) d)))
--             (fcross0≡0 (apply g (fsplice b c))) ⟩
--   fsuc (fcross (apply (remove (fsplice b c) g) (fcross c b))
--                (fcross (apply g (fsplice b c)) d))
--     ≡⟨ cong fsuc (fcross-appply-remove-splice-fcross-fcross-apply-fsplice b c d g) ⟩
--   fsuc (fcross (apply (remove b g) c)
--                ((fcross (apply g b)) d))
--     ≡⟨ refl ⟩
--   fcross (apply (inc f0 (remove b g)) (fsuc c))
--          (fsuc ((fcross (apply g b)) d))
--     ≡⟨ cong (λ ○ → fcross (apply (inc ○ (remove b g)) (fsuc c))
--             (fsuc ((fcross (apply g b)) d))) (sym (fcross0≡0 (apply g b))) ⟩
--   fcross (apply (inc (fcross (apply g b) fzero) (remove b g)) (fsuc c))
--          (fsuc ((fcross (apply g b)) d))
--     ≡⟨ refl ⟩
--   fcross (apply (remove (fsuc b) (inc fzero g)) (fsuc c))
--          (fcross (apply (inc fzero g) (fsuc b)) (fsuc d)) ▯
-- fcross-appply-remove-splice-fcross-fcross-apply-fsplice (fsuc b) (fsuc c) (fsuc d) (inc (fsuc e) g) =
--   fcross (apply (remove (fsplice (fsuc b) (fsuc c)) (inc (fsuc e) g)) (fcross (fsuc c) (fsuc b)))
--          (fcross (apply (inc (fsuc e) g) (fsplice (fsuc b) (fsuc c))) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (remove (fsuc (fsplice b c)) (inc (fsuc e) g)) (fsuc (fcross c b)))
--          (fcross (apply (inc (fsuc e) g) (fsuc (fsplice b c))) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (inc (fcross (apply g (fsplice b c)) (fsuc e)) (remove (fsplice b c) g))
--                 (fsuc (fcross c b)))
--          (fcross (fsplice (fsuc e) (apply g (fsplice b c))) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (fsplice (fcross (apply g (fsplice b c)) (fsuc e))
--                   (apply (remove (fsplice b c) g) (fcross c b)))
--          (fcross (fsplice (fsuc e) (apply g (fsplice b c))) (fsuc d))
--     ≡⟨ {!!} ⟩
--   fcross (fsplice (fcross (apply g b) (fsuc e)) (apply (remove b g) c))
--          (fcross (fsplice (fsuc e) (apply g b)) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (inc (fcross (apply g b) (fsuc e)) (remove b g)) (fsuc c))
--          (fcross (fsplice (fsuc e) (apply g b)) (fsuc d))
--     ≡⟨ refl ⟩
--   fcross (apply (remove (fsuc b) (inc (fsuc e) g)) (fsuc c))
--          (fcross (apply (inc (fsuc e) g) (fsuc b)) (fsuc d)) ▯

-- remove-cross-remove-fsplice
--   : {m n : ℕ} (b : Fin (suc (suc m))) (c : Fin (suc m))
--   → (g : Inj (suc (suc m)) (suc (suc n))) 
--   → remove (fcross c b) (remove (fsplice b c) g)
--   ≡ remove c (remove b g)
-- remove-cross-remove-fsplice {m} {n} fzero fzero (inc d g) = refl
-- remove-cross-remove-fsplice {m} {n} fzero (fsuc c) (inc d g) = refl
-- remove-cross-remove-fsplice {m} {n} (fsuc b) fzero (inc d g) = refl
-- remove-cross-remove-fsplice {suc m} {suc n} (fsuc b) (fsuc c) (inc d g) =
--   remove (fcross (fsuc c) (fsuc b))
--    (remove (fsplice (fsuc b) (fsuc c)) (inc d g))
--     ≡⟨ refl ⟩
--   remove (fsuc (fcross c b))
--          (inc (fcross (apply g (fsplice b c)) d) (remove (fsplice b c) g))
--     ≡⟨ refl ⟩
--   inc (fcross (apply (remove (fsplice b c) g) (fcross c b))
--               (fcross (apply g (fsplice b c)) d))
--       (remove (fcross c b) (remove (fsplice b c) g))
--     ≡⟨ cong₂ inc u v ⟩
--   inc (fcross (apply (remove b g) c) (fcross (apply g b) d))
--       (remove c (remove b g))
--     ≡⟨ refl ⟩
--   remove (fsuc c) (inc (fcross (apply g b) d) (remove b g))
--     ≡⟨ refl ⟩
--   remove (fsuc c) (remove (fsuc b) (inc d g)) ▯
--   where
--     u : fcross (apply (remove (fsplice b c) g) (fcross c b))
--          (fcross (apply g (fsplice b c)) d)
--          ≡ fcross (apply (remove b g) c) (fcross (apply g b) d)
--     u = fcross (apply (remove (fsplice b c) g) (fcross c b))
--                (fcross (apply g (fsplice b c)) d)
--           ≡⟨ {!!} ⟩
--         fcross (apply (remove b g) c) (fcross (apply g b) d) ▯
--     v : remove (fcross c b) (remove (fsplice b c) g) ≡
--          remove c (remove b g)
--     v = remove (fcross c b) (remove (fsplice b c) g)
--           ≡⟨ remove-cross-remove-fsplice b c g ⟩
--         remove c (remove b g) ▯

-- remove-comp : ∀ {l m n : ℕ} (f : Inj (suc l) (suc m))
--             → (g : Inj (suc m) (suc n)) (a : Fin (suc l))
--             → (remove (apply f a) g ∘ʲ remove a f) ≡ remove a (g ∘ʲ f)
-- remove-comp (inc b f) g fzero = refl
-- remove-comp {l = suc l} {m = suc m} {n = zero} (inc b f) (inc _ ())
-- remove-comp {l = suc l} {m = suc m} {n = suc n} (inc b f) g (fsuc a) =
--   remove (apply (inc b f) (fsuc a)) g ∘ʲ remove (fsuc a) (inc b f)
--     ≡⟨ refl ⟩
--   remove (fsplice b (apply f a)) g ∘ʲ remove (fsuc a) (inc b f)
--     ≡⟨ refl ⟩
--   remove (fsplice b (apply f a)) g ∘ʲ inc (fcross (apply f a) b) (remove a f)
--     ≡⟨ refl ⟩
--   inc (apply (remove (fsplice b (apply f a)) g) (fcross (apply f a) b))
--       (remove (fcross (apply f a) b) (remove (fsplice b (apply f a)) g) ∘ʲ remove a f)
--     ≡⟨ cong₂ inc u v ⟩
--   inc (fcross (apply (remove b g ∘ʲ f) a) (apply g b)) (remove a (remove b g ∘ʲ f))
--     ≡⟨ refl ⟩
--   remove (fsuc a) (inc (apply g b) (remove b g ∘ʲ f))
--     ≡⟨ refl ⟩
--   remove (fsuc a) (g ∘ʲ inc b f) ▯
--   where
--     u : apply (remove (fsplice b (apply f a)) g) (fcross (apply f a) b)
--       ≡ fcross (apply (remove b g ∘ʲ f) a) (apply g b)
--     u = {!!}
--     w : (d : Fin (suc m))
--       → remove (fcross d b) (remove (fsplice b d) g)
--       ≡ remove d (remove b g)
--     w = {!!} 
--     v : remove (fcross (apply f a) b) (remove (fsplice b (apply f a)) g) ∘ʲ remove a f
--       ≡ remove a (remove b g ∘ʲ f)
--     v = remove (fcross (apply f a) b) (remove (fsplice b (apply f a)) g)
--                ∘ʲ remove a f
--           ≡⟨ cong (_∘ʲ remove a f) (w (apply f a)) ⟩
--         remove (apply f a) (remove b g) ∘ʲ remove a f
--           ≡⟨ remove-comp f (remove b g) a ⟩
--         remove a (remove b g ∘ʲ f) ▯


removeId : ∀ {m : ℕ} (a : Fin (suc m)) → remove a (idInj (suc m)) ≡ idInj m
removeId fzero = refl
removeId {m = zero} (fsuc a) = Fin0-absurd a
removeId {m = suc m} (fsuc a) =
  remove (fsuc a) (idInj (suc (suc m)))
    ≡⟨ refl ⟩
  remove (fsuc a) (inc fzero (idInj (suc m)))
    ≡⟨ refl ⟩
  inc (fcross (apply (idInj (suc m)) a) f0) (remove a (idInj (suc m)))
    ≡⟨ cong (λ ○ → inc ○ (remove a (idInj (suc m)))) ( ≈ᶠ→≡ u') ⟩
  inc f0 (remove a (idInj (suc m)))
    ≡⟨ cong (inc f0) (removeId a) ⟩
  idInj (suc m) ▯
  where
    u : fcross (apply ((idInj (suc m))) a) (f0 {suc m}) ≈ᶠ (f0 {suc m})
    u = ≤→fcross≈id (apply ((idInj (suc m))) a) f0
                    (fzero≤a (apply (inc f0 (idInj m)) a))
    u' : fcross (apply (idInj (suc m)) a) (f0 {suc m}) ≈ᶠ (f0 {m})
    u' = ≈ᶠ-trans u ≈fzero

∘ʲ-idL : ∀ {m n : ℕ} (f : Inj m n) → idInj n ∘ʲ f ≡ f
∘ʲ-idL (nul _) = refl
∘ʲ-idL {n = suc n} (inc b f) =
 idInj (suc n) ∘ʲ inc b f
   ≡⟨ refl ⟩
 inc (apply (idInj (suc n)) b) (remove b (idInj (suc n)) ∘ʲ f)
   ≡⟨ cong₂ inc (applyId b) refl ⟩
 inc b (remove b (idInj (suc n)) ∘ʲ f)
   ≡⟨ cong (λ ○ → inc b (○ ∘ʲ f)) (removeId b) ⟩
 inc b (idInj n ∘ʲ f)
   ≡⟨ cong₂ inc refl (∘ʲ-idL f) ⟩
 inc b f ▯

∘ʲ-idR : ∀ {m n : ℕ} (f : Inj m n) → f ∘ʲ idInj m ≡ f
∘ʲ-idR (nul _) = refl
∘ʲ-idR {m = suc m} (inc b f) =
  inc b f ∘ʲ idInj (suc m)
    ≡⟨ refl ⟩
  inc b f ∘ʲ inc fzero (idInj m)
    ≡⟨ cong (inc b) (∘ʲ-idR f) ⟩
  inc b f ▯

fsplice-apply-fsplice
  : {m n : ℕ} (a : Fin (suc m)) (b : Fin m) (c : Fin (suc (suc n)))
  → (f : Inj (suc m) (suc n))
  → fsplice c (apply f (fsplice a b))
  ≡ fsplice (fsplice c (apply f a))
            (fsplice (fcross (apply f a) c)
                    (apply (remove a f) b))
fsplice-apply-fsplice fzero fzero c (inc d f) =
  fsplice c (apply (inc d f) (fsplice f0 f0))
    ≡⟨ refl ⟩
  fsplice c (apply (inc d f) f1)
    ≡⟨ refl ⟩
  fsplice c (fsplice d (apply f f0))
    ≡⟨ sym (fsplice-fsplice-fsplice-fcross c (apply f f0) d) ⟩
  fsplice (fsplice c d) (fsplice (fcross d c) (apply f f0))
    ≡⟨ refl ⟩
  fsplice (fsplice c (apply (inc d f) f0))
   (fsplice (fcross (apply (inc d f) f0) c)
    (apply (remove f0 (inc d f)) f0)) ▯ 
fsplice-apply-fsplice fzero (fsuc b) c (inc d f) =
  fsplice c (apply (inc d f) (fsplice f0 (fsuc b)))
    ≡⟨ refl ⟩
  fsplice c (fsplice d (apply f (fsuc b)))
    ≡⟨ sym (fsplice-fsplice-fsplice-fcross c (apply f (fsuc b)) d) ⟩
  fsplice (fsplice c d) (fsplice (fcross d c) (apply f (fsuc b)))
    ≡⟨ refl ⟩
  fsplice (fsplice c (apply (inc d f) f0))
   (fsplice (fcross (apply (inc d f) f0) c)
    (apply (remove f0 (inc d f)) (fsuc b))) ▯ 
fsplice-apply-fsplice {suc m} {suc n} (fsuc a) fzero c (inc d f) =
  fsplice c (apply (inc d f) (fsplice (fsuc a) f0))
    ≡⟨ refl ⟩
  fsplice c d 
    ≡⟨ cong (fsplice c) (sym (fsplice-fsplice-fcross d (apply f a))) ⟩
  fsplice c (fsplice (fsplice d (apply f a)) (fcross (apply f a) d)) 
    ≡⟨ sym (fsplice-fsplice-fsplice-fcross
         c (fcross (apply f a) d) (fsplice d (apply f a)) ) ⟩
  fsplice (fsplice c (fsplice d (apply f a)))
   (fsplice (fcross (fsplice d (apply f a)) c)
    (fcross (apply f a) d))
    ≡⟨ refl ⟩
  fsplice (fsplice c (apply (inc d f) (fsuc a)))
   (fsplice (fcross (apply (inc d f) (fsuc a)) c)
    (apply (remove (fsuc a) (inc d f)) f0)) ▯
fsplice-apply-fsplice {suc m} {suc n} (fsuc a) (fsuc b) c (inc d f) =
  fsplice c (apply (inc d f) (fsplice (fsuc a) (fsuc b)))
    ≡⟨ refl ⟩
  fsplice c (apply (inc d f) (fsuc (fsplice a b)))
    ≡⟨ refl ⟩
  fsplice c (fsplice d (apply f (fsplice a b)))
    ≡⟨ cong (fsplice c) (fsplice-apply-fsplice a b d f) ⟩
  fsplice c
   (fsplice (fsplice d (apply f a))
    (fsplice (fcross (apply f a) d) (apply (remove a f) b)))
    ≡⟨ refl ⟩
  fsplice c
   (fsplice (fsplice d (apply f a))
    (apply (inc (fcross (apply f a) d) (remove a f)) (fsuc b)))
    ≡⟨ sym (fsplice-fsplice-fsplice-fcross c
         (apply (inc (fcross (apply f a) d) (remove a f)) (fsuc b))
         (fsplice d (apply f a))) ⟩
  fsplice (fsplice c (fsplice d (apply f a)))
   (fsplice (fcross (fsplice d (apply f a)) c)
    (apply (inc (fcross (apply f a) d) (remove a f) ) (fsuc b)))
    ≡⟨ refl ⟩
  fsplice (fsplice c (apply (inc d f) (fsuc a)))
   (fsplice (fcross (apply (inc d f) (fsuc a)) c)
    (apply (remove (fsuc a) (inc d f)) (fsuc b))) ▯ 

apply-fsplice-apply
  : ∀ {m n : ℕ} → (f : Inj (suc m) (suc n))
  → (a : Fin (suc m)) (b : Fin m)
  → apply f (fsplice a b)
  ≡ fsplice (apply f a) (apply (remove a f) b)
apply-fsplice-apply (inc c f) fzero b = refl
apply-fsplice-apply {suc m} {suc n} (inc c f) (fsuc a) fzero =
  apply (inc c f) (fsplice (fsuc a) f0) ≡⟨ refl ⟩
  apply (inc c f) f0 ≡⟨ refl ⟩
  c ≡⟨ sym (fsplice-fsplice-fcross c (apply f a)) ⟩
  fsplice (fsplice c (apply f a)) (fcross (apply f a) c) ≡⟨ refl ⟩
  fsplice (fsplice c (apply f a)) 
          (apply (inc (fcross (apply f a) c) (remove a f)) f0) ≡⟨ refl ⟩
  fsplice (apply (inc c f) (fsuc a))
          (apply (remove (fsuc a) (inc c f)) f0) ▯
apply-fsplice-apply {suc m} {suc n} (inc c f) (fsuc a) (fsuc b) =
  apply (inc c f) (fsplice (fsuc a) (fsuc b))
    ≡⟨ refl ⟩
  apply (inc c f) (fsuc (fsplice a b))
    ≡⟨ refl ⟩
  fsplice c (apply f (fsplice a b))
    ≡⟨ fsplice-apply-fsplice a b c f ⟩
  fsplice (fsplice c (apply f a))
          (fsplice (fcross (apply f a) c)
                   (apply (remove a f) b))
    ≡⟨ refl ⟩
  fsplice (apply (inc c f) (fsuc a))
   (apply (inc (fcross (apply f a) c) (remove a f)) (fsuc b))
    ≡⟨ refl ⟩
  fsplice (apply (inc c f) (fsuc a))
   (apply (remove (fsuc a) (inc c f)) (fsuc b)) ▯

apply-apply
  : ∀ {l m n : ℕ} → (g : Inj m n) (f : Inj l m) (a : Fin l)
  → apply g (apply f a) ≡ apply (g ∘ʲ f) a
apply-apply {suc l} {suc m} {suc n} g (inc b f) fzero = refl
apply-apply {suc l} {suc m} {suc n} g (inc b f) (fsuc a) =
  apply g (apply (inc b f) (fsuc a))
    ≡⟨ refl ⟩
  apply g (fsplice b (apply f a))
    ≡⟨ apply-fsplice-apply g b (apply f a) ⟩
  fsplice (apply g b) (apply (remove b g) (apply f a))
    ≡⟨ cong (fsplice (apply g b)) (apply-apply (remove b g) f a) ⟩
  fsplice (apply g b) (apply (remove b g ∘ʲ f) a)
    ≡⟨ refl ⟩
  apply (inc (apply g b) (remove b g ∘ʲ f)) (fsuc a)
    ≡⟨ refl ⟩
  apply (g ∘ʲ inc b f) (fsuc a) ▯

∘ʲ-assoc : ∀ {k l m n : ℕ} → (h : Inj m n) → (g : Inj l m) → (f : Inj k l)
         → h ∘ʲ (g ∘ʲ f) ≡ (h ∘ʲ g) ∘ʲ f
∘ʲ-assoc {zero} {l} {m} {n} h g (nul _) = refl
∘ʲ-assoc {suc k} {suc l} {suc m} {suc n} h g f =
  injExt (h ∘ʲ (g ∘ʲ f)) ((h ∘ʲ g) ∘ʲ f) apply-eq
  where
    apply-eq : (a : Fin (suc k)) → apply (h ∘ʲ (g ∘ʲ f)) a
             ≡ apply ((h ∘ʲ g) ∘ʲ f) a
    apply-eq a =
      apply (h ∘ʲ (g ∘ʲ f)) a ≡⟨ sym (apply-apply h (g ∘ʲ f) a) ⟩
      apply h (apply (g ∘ʲ f) a) ≡⟨ cong (apply h) (sym (apply-apply g f a)) ⟩
      apply h (apply g (apply f a)) ≡⟨ apply-apply h g (apply f a) ⟩
      apply (h ∘ʲ g) (apply f a) ≡⟨ apply-apply (h ∘ʲ g) f a ⟩
      apply ((h ∘ʲ g) ∘ʲ f) a ▯
