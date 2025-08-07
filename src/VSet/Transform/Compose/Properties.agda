module VSet.Transform.Compose.Properties where

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
open import VSet.Transform.Compose.Base
open import VSet.Transform.Elementary.Base

applyId : ∀ {m : ℕ} (a : Fin m) → apply (idInj m) a ≡ a
applyId fzero = refl
applyId (fsuc a) = cong fsuc (applyId a)

removeId : ∀ {m : ℕ} (a : Fin (suc m)) → remove a (idInj (suc m)) ≡ idInj m
removeId fzero = refl
removeId {m = m} (fsuc a) =
  remove (fsuc a) (idInj (suc m))
    ≡⟨ refl ⟩
  remove (fsuc a) (inc fzero (idInj m))
    ≡⟨ {!!} ⟩
  idInj m ▯

∘ʲ-idL : ∀ {m n : ℕ} (f : Inj m n) → idInj n ∘ʲ f ≡ f
∘ʲ-idL (nul _) = refl
∘ʲ-idL {n = suc n} (inc b f) =
 idInj (suc n) ∘ʲ inc b f
   ≡⟨ refl ⟩
 inc (apply (idInj (suc n)) b) (remove b (idInj (suc n)) ∘ʲ f)
   ≡⟨ cong₂ inc (applyId b) {!!} ⟩
 inc b (remove b (idInj (suc n)) ∘ʲ f)
   ≡⟨ cong₂ inc {!∘ʲ-idL!} {!!} ⟩
 inc b f ▯

∘ʲ-idR : ∀ {m n : ℕ} (f : Inj m n) → f ∘ʲ idInj m ≡ f
∘ʲ-idR (nul _) = refl
∘ʲ-idR {m = suc m} (inc b f) =
  inc b f ∘ʲ idInj (suc m)
    ≡⟨ refl ⟩
  inc b f ∘ʲ inc fzero (idInj m)
    ≡⟨ cong (inc b) (∘ʲ-idR f) ⟩
  inc b f ▯

-- ∘ʲ-assoc : ∀ {k l m n : ℕ} → (h : Inj m n) → (g : Inj l m) → (f : Inj k l)
--          → h ∘ʲ (g ∘ʲ f) ≡ (h ∘ʲ g) ∘ʲ f
-- ∘ʲ-assoc (nul _) (nul _) (nul _) = refl
-- ∘ʲ-assoc (inc _ _) _ (nul _) = refl
-- ∘ʲ-assoc (inc c h) (inc b g) (inc a f) =
--  inc c h ∘ʲ (inc b g ∘ʲ inc a f)
--    ≡⟨ refl ⟩
--  inc (apply (inc c h) (apply (inc b g) a))
--      (remove (apply (inc b g) a) (inc c h) ∘ʲ (remove a (inc b g) ∘ʲ f))
--    ≡⟨ {!!} ⟩
--  inc (apply (inc (apply (inc c h) b) (remove b (inc c h) ∘ʲ g)) a)
--      (remove a (inc (apply (inc c h) b) (remove b (inc c h) ∘ʲ g)) ∘ʲ f)
--    ≡⟨ refl ⟩
--  (inc c h ∘ʲ inc b g) ∘ʲ inc a f ▯
--  where
--    u : apply (inc c h) (apply (inc b g) a)
--      ≡ apply (inc (apply (inc c h) b) (remove b (inc c h) ∘ʲ g)) a
--    u = {!!}

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
    ≡⟨ sym {!!} ⟩
  fsplice (fsplice c (apply f a))
          (fsplice (fcross (apply f a) c)
                   (apply (remove a f) b))
    ≡⟨ {!!} ⟩
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
    ≡⟨ {!!} ⟩
  fsplice (apply g b) (apply (remove b g) (apply f a))
    ≡⟨ cong (fsplice (apply g b)) (apply-apply (remove b g) f a) ⟩
  fsplice (apply g b) (apply (remove b g ∘ʲ f) a)
    ≡⟨ refl ⟩
  apply (inc (apply g b) (remove b g ∘ʲ f)) (fsuc a)
    ≡⟨ refl ⟩
  apply (g ∘ʲ inc b f) (fsuc a) ▯

∘ʲ-assoc : ∀ {k l m n : ℕ} → (h : Inj m n) → (g : Inj l m) → (f : Inj k l)
         → h ∘ʲ (g ∘ʲ f) ≡ (h ∘ʲ g) ∘ʲ f
∘ʲ-assoc h g (nul _) = refl
∘ʲ-assoc {suc k} {suc l} {suc m} {suc n} h g (inc a f) =
 h ∘ʲ (g ∘ʲ inc a f)
   ≡⟨ refl ⟩
 h ∘ʲ (inc (apply g a) (remove a g ∘ʲ f))
   ≡⟨ refl ⟩
 inc (apply h (apply g a))
     (remove (apply g a) h ∘ʲ (remove a g ∘ʲ f))
   ≡⟨ {!!} ⟩
 inc (apply (h ∘ʲ g) a) (remove a (h ∘ʲ g) ∘ʲ f)
   ≡⟨ refl ⟩
 (h ∘ʲ g) ∘ʲ inc a f ▯
