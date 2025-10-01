module VSet.Transform.Inj.Compose.Properties where

open import Cubical.Data.List.Base hiding ([_])
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Prod.Base hiding (map)

open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base
open import VSet.Data.Inj.Properties
open import VSet.Data.Nat.Properties
open import VSet.Prelude
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Elementary.Base

applyId : ∀ {m : ℕ} (a : Fin m) → apply (idInj m) a ≡ a
applyId fzero = refl
applyId (fsuc a) = cong fsuc (applyId a)

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

transportInj-peel
  : ∀ {l m : ℕ} (p : suc l ≡ suc m)
  → transportInj p ≡ inc f0 (transportInj (cong predℕ p))
transportInj-peel {l} {m} p =
  transportInj p
    ≡⟨ refl ⟩
  subst2 Inj refl p (inc fzero (Id {l}))
    ≡⟨ cong (λ ○ → subst2 Inj refl ○ (inc fzero (Id {l}))) (sym (path-suc-pred p)) ⟩
  subst2 Inj refl (cong (suc ∘ predℕ) p) (inc fzero (Id {l}))
    ≡⟨ subst2-inc-reorder refl (cong predℕ p) fzero (Id {l}) ⟩
  inc (subst Fin (cong (suc ∘ predℕ) p) f0) (subst2 Inj refl (cong predℕ p) Id)
    ≡⟨ cong₂ inc r refl ⟩
  inc f0 (transportInj (cong predℕ p)) ▯
  where
    r : subst Fin (cong (suc ∘ predℕ) p) f0 ≡ f0
    r = sym (fzero≡subst-fzero (cong predℕ p))

transportInj-isId
  : ∀ {l m : ℕ} (p : l ≡ m) (x : Fin l)
  → apply (transportInj p) x ≡ subst Fin p x
transportInj-isId {suc l} {zero} p x = absurd (snotz p)
transportInj-isId {suc l} {suc m} p fzero =
  apply (transportInj p) fzero
    ≡⟨ cong (λ ○ → apply ○ fzero) (transportInj-peel p) ⟩
  apply (inc fzero (transportInj (cong predℕ p))) fzero
    ≡⟨ refl ⟩
  fzero {m}
    ≡⟨ fzero≡subst-fzero (cong predℕ p) ⟩
  subst Fin (cong (suc ∘ predℕ) p) (fzero {l})
    ≡⟨ cong (λ ○ → subst Fin ○ (fzero {l})) (path-suc-pred p) ⟩
  subst Fin p (fzero {l}) ▯
transportInj-isId {suc (suc l)} {suc zero} p (fsuc x) = absurd (snotz (cong predℕ p))
transportInj-isId {suc (suc l)} {suc (suc m)} p (fsuc x) =
  apply (transportInj p) (fsuc x)
    ≡⟨ cong (λ ○ → apply ○ (fsuc x)) (transportInj-peel p) ⟩
  apply (inc fzero (transportInj (cong predℕ p))) (fsuc x)
    ≡⟨ refl ⟩
  fsplice fzero (apply (transportInj (cong predℕ p)) x)
    ≡⟨ refl ⟩
  fsuc (apply (transportInj (cong predℕ p)) x)
    ≡⟨ cong fsuc (transportInj-isId (cong predℕ p) x) ⟩
  fsuc (subst Fin (cong predℕ p) x)
    ≡⟨ sym (subst-fsuc-reorder (cong predℕ p) x) ⟩
  subst Fin (cong (suc ∘ predℕ) p) (fsuc x)
    ≡⟨ cong (λ ○ → subst Fin ○ (fsuc x)) (path-suc-pred p) ⟩
  subst Fin p (fsuc x) ▯

transportInj-idR-ext
  : ∀ {l m n : ℕ} (p : l ≡ m) (f : Inj m n) (x : Fin l)
  → apply (f ∘ʲ transportInj p) x ≡ apply (subst2 Inj (sym p) refl f) x
transportInj-idR-ext {l} {m} {n} p f x =
  apply (f ∘ʲ transportInj p) x
    ≡⟨ sym (apply-apply f (transportInj p) x) ⟩
  apply f (apply (transportInj p) x)
    ≡⟨ cong (apply f) (transportInj-isId p x) ⟩
  apply f (subst Fin p x)
    ≡⟨ {!!} ⟩
  apply (subst2 Inj (sym p) refl f) x ▯

-- transportInj-idR-ext : ∀ {l m n : ℕ} (p : l ≡ m) (f : Inj m n) (x : Fin l)
--                 → apply (f ∘ʲ transportInj p) x ≡ apply (subst2 Inj (sym p) refl f) x
-- transportInj-idR-ext {suc l} {0} {n} p (nul n) x = absurd (snotz p)
-- transportInj-idR-ext {suc l} {suc m} {suc n} p (inc b f) fzero =
--   apply (inc b f ∘ʲ transportInj p) fzero
--     ≡⟨ sym (apply-apply (inc b f) (transportInj p) fzero) ⟩
--   apply (inc b f) (apply (transportInj p) fzero)
--     ≡⟨ {!!} ⟩
--   subst Fin refl b
--     ≡⟨ refl ⟩
--   apply (inc (subst Fin refl b) f) fzero
--     ≡⟨ cong (λ ○ → apply ○ fzero)
--             (sym (subst2-inc-reorder
--               (sym (cong predℕ p)) refl b f)) ⟩
--   apply (transport (λ i → Inj (suc (predℕ (p (~ i)))) (suc n)) (inc b f)) fzero
--     ≡⟨ (λ j → apply (transport (λ i → Inj (path-suc-pred (sym p) j i) (suc n)) (inc b f)) fzero) ⟩
--   apply (subst2 Inj (sym p) refl (inc b f)) fzero ▯
-- transportInj-idR-ext {suc l} {m} {n} p f (fsuc x) = {!!}

-- transportInj-idR : ∀ {l m n : ℕ} (p : l ≡ m) (f : Inj m n)
--                 → f ∘ʲ transportInj p ≡ subst2 Inj (sym p) refl f
-- transportInj-idR {l} {m} {n} p f =
--   injExt (f ∘ʲ transportInj p) (subst2 Inj (sym p) refl f)
--          (transportInj-idR-ext p f )

-- FinFun : ℕ → ℕ → Type _
-- FinFun m n = Fin m → Fin n

-- -- transportInj-idR' : ∀ {l m n : ℕ} (p : l ≡ m) (f : Fin m → Fin n)
-- --                 → subst (λ x → FinFun x n) (sym p) (f ∘ id)
-- --                 ≡ f ∘ subst (FinFun l) p (id {A = Fin l})
-- -- transportInj-idR' {l} {m} {n} p f =
-- --   substCommSlice Fin (λ x → FinFun x n) {!!} {!!} {!!}

-- -- transportInj-idR {zero} {zero} p (nul n) with inspect' (transportInj p)
-- -- ... | nul 0 , q = 
-- --   nul n ∘ʲ transportInj p ≡⟨ cong (nul n ∘ʲ_) q ⟩
-- --   nul n ∘ʲ nul 0 ≡⟨ refl ⟩
-- --   nul n ≡⟨ nul≡subst2-nul (sym p) refl ⟩
-- --   subst2 Inj (sym p) refl (nul n) ▯
-- -- transportInj-idR {suc l} {zero} p (nul n) = absurd (snotz p)
-- -- transportInj-idR {zero} {suc m} p f = absurd (znots p)
-- -- transportInj-idR {suc l} {suc m} p f =
-- --   f ∘ʲ transportInj p ≡⟨ {!!} ⟩
-- --   subst2 Inj (sym p) refl f ▯

