module VSet.Transform.Inverse.Properties where

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
open import VSet.Transform.Inverse.Base
open import VSet.Transform.Inverse.Insert
open import VSet.Transform.Compose.Base
open import Cubical.Data.Maybe.Base hiding (elim)

private
  variable
    l l' m m' n n' : ℕ

inv-is-apply-inv : ∀ {m} → (f : Inj m m) → (y : Fin m)
                 → apply-inv f y ≡ just (apply (inv f) y)
inv-is-apply-inv {suc m} (inc b f) y with y ≈?ᶠ b
... | yes y≈b =
  apply-inv-rec f b y (yes y≈b) ≡⟨ refl ⟩
  just fzero ≡⟨ cong just (sym (apply-insert≡b b f0 (inv f))) ⟩
  just (apply (insert b f0 (inv f)) b)
    ≡⟨ cong (λ ○ → just (apply (insert b f0 (inv f)) ○)) (≈ᶠ→≡ (≈fsym y≈b)) ⟩
  just (apply (insert b f0 (inv f)) y) ▯
... | no y≢b =
  apply-inv-rec f b y (no y≢b)
    ≡⟨ refl ⟩
  map-Maybe fsuc (apply-inv f (funsplice b y y≢b))
    ≡⟨ cong (map-Maybe fsuc) (inv-is-apply-inv f (funsplice b y y≢b)) ⟩
  map-Maybe fsuc (just (apply (inv f) (funsplice b y y≢b)))
    ≡⟨ refl ⟩
  just (fsuc (apply (inv f) (funsplice b y y≢b)))
    ≡⟨ {!!} ⟩
  just (apply (insert b f0 (inv f)) y) ▯

-- inv-is-apply-inv : ∀ {m} → (f : Inj m m) → (y : Fin m)
--                  → apply-inv f y ≡ just (apply (inv f) y)
-- inv-is-apply-inv (inc b f) y with y ≈? b
-- inv-is-apply-inv (inc b f) y | no y≉b =
--   apply-inv-rec f b y (no y≉b)
--     ≡⟨ {!!} ⟩
--   map-Maybe fsuc (apply-inv f {!funsplice b y y≉b!})
--     ≡⟨ cong (map-Maybe fsuc) (inv-is-apply-inv f {!funsplice b y y≉b!}) ⟩
--   map-Maybe fsuc (just (apply (inv f) {!funsplice b y y≢b!}))
--     ≡⟨ refl ⟩
--   just (fsuc (apply (inv f) {!funsplice b y y≉b!}))
--     ≡⟨ cong just (sym {!≢→apply-insert≡fsuc-apply b (inv f) y y≉b!}) ⟩
--   just (apply (insert b f0 (inv f)) y) ▯
-- inv-is-apply-inv {m = suc (suc m)} (inc b f) y | yes y≡b =
--   apply-inv-rec {m = suc m} f b y (yes y≡b)
--     ≡⟨ refl ⟩
--   just fzero
--     ≡⟨ cong just {!!} ⟩
--   just (apply (insert b f0 (inv f)) y) ▯
-- inv-is-apply-inv {m = suc m} (inc b f) y = {!!}

-- inv-is-apply-inv : ∀ {m} → (f : Inj m m) → (y : Fin m) → apply-inv f y ≡ just (apply (inv f) y)
-- inv-is-apply-inv (inc fzero f) fzero = ?
-- inv-is-apply-inv (inc fzero f) (fsuc y) =
--   let rec : apply-inv f y ≡ just (apply (inv f) y)
--       rec = inv-is-apply-inv f y
--   in apply-inv (inc f0 f) (fsuc y) ≡⟨ refl ⟩
--      map-Maybe fsuc (apply-inv f y)
--        ≡⟨ cong (map-Maybe fsuc) (inv-is-apply-inv f y) ⟩
--      map-Maybe fsuc (just (apply (inv f) y)) ≡⟨ refl ⟩
--      just (fsuc (apply (inv f) y)) ≡⟨ refl ⟩
--      just (fsplice f0 (apply (inv f) y)) ≡⟨ refl ⟩
--      just (apply (inc f0 (inv f)) (fsuc y)) ≡⟨ refl ⟩
--      just (apply (insert f0 f0 (inv f)) (fsuc y)) ≡⟨ refl ⟩
--      just (apply (inv (inc f0 f)) (fsuc y)) ▯
-- -- inv-is-apply-inv (inc (fsuc b) f) fzero =
-- --   let rec : apply-inv f fzero ≡ just (apply (inv f) fzero)
-- --       rec = inv-is-apply-inv f fzero 
-- --   in apply-inv (inc f0 f) fzero ≡⟨ refl ⟩
-- --      map-Maybe fsuc (apply-inv f y)
-- --        ≡⟨ cong (map-Maybe fsuc) (inv-is-apply-inv f y) ⟩
-- --      map-Maybe fsuc (just (apply (inv f) y)) ≡⟨ refl ⟩
-- --      just (fsuc (apply (inv f) y)) ≡⟨ refl ⟩
-- --      just (fsplice f0 (apply (inv f) y)) ≡⟨ refl ⟩
-- --      just (apply (inc f0 (inv f)) (fsuc y)) ≡⟨ refl ⟩
-- --      just (apply (insert f0 f0 (inv f)) (fsuc y)) ≡⟨ refl ⟩
-- --      just (apply (inv (inc f0 f)) (fsuc y)) ▯
-- -- inv-is-apply-inv (inc (fsuc b) f) (fsuc y) = {!!}


+suc : ∀ {m n} → m + suc n ≡ suc (m + n)
+suc {zero} {n} = refl
+suc {suc m} {n} = cong suc (+-suc m n)

insert0≡inc
  : ∀ {m} (b : Fin (suc m)) (f : Inj m m)
  → insert fzero b f ≡ inc b f
insert0≡inc b f = refl

-- Not sure if this is the easiest way to prove it. There are a lot of cases.
insert-reorder : ∀ {m n} (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                         (b1 : Fin (suc n)) (b2 : Fin (suc (suc n)))
               → (f : Inj m n)
               → insert a2 b2 (insert a1 b1 f)
               ≡ insert (fsplice a2 a1) (fsplice b2 b1)
                   (insert (antisplice a1 a2) (antisplice b1 b2) f)
insert-reorder fzero fzero b1 b2 f =
  insert f0 b2 (insert f0 b1 f)
    ≡⟨ refl ⟩
  inc b2 (inc b1 f)
    ≡⟨ {!!} ⟩
  insert f1 (fsplice b2 b1)
   (inc (antisplice b1 b2) f)
    ≡⟨ refl ⟩
  insert (fsplice f0 f0) (fsplice b2 b1)
   (insert (antisplice f0 f0) (antisplice b1 b2) f) ▯
insert-reorder (fsuc a1) a2 b1 b2 f = {!!}
insert-reorder fzero (fsuc a2) b1 b2 f = {!!}
  -- insert a2 b2 (insert a1 b1 f)
  --   ≡⟨ {!!} ⟩
  -- insert (fsplice a2 a1) (fsplice b2 b1)
  --  (insert (antisplice a1 a2) (antisplice b1 b2) f) ▯

insert-comp
  : ∀ {l m n : ℕ} (b : Fin (suc m)) (f : Inj l m) (g : Inj m n)
  → insert b f0 g ∘ʲ insert f0 b f ≡ insert f0 f0 (g ∘ʲ f)
insert-comp fzero f g = refl
insert-comp (fsuc b) f (inc c g) =
  insert (fsuc b) f0 (inc c g) ∘ʲ insert f0 (fsuc b) f
    ≡⟨ refl ⟩
  insert (fsuc b) f0 (inc c g) ∘ʲ inc (fsuc b) f
    ≡⟨ {!!} ⟩
  insert f0 f0 (inc c g ∘ʲ f) ▯

insert-isInjective
  : ∀ {m} {a b : Fin (suc m)} {f g : Inj m m}
  → insert a b f ≡ insert a b g  → f ≡ g
insert-isInjective {a = fzero} {b = b} {f = f} {g = g} f'≡g' =
  proj₂ (inc-isInjective f'≡g')
insert-isInjective {a = fsuc a} {b = fzero} {f = inc c1 f} {g = inc c2 g} f''≡g'' =
  let ins-f≡ins-g : insert a f0 f ≡ insert a f0 g
      ins-f≡ins-g = (proj₂ (inc-isInjective f''≡g''))
      f≡g : f ≡ g
      f≡g = insert-isInjective ins-f≡ins-g
      c1≡c2 : c1 ≡ c2
      c1≡c2 = fsuc-injective $ proj₁ $ inc-isInjective f''≡g''
  in cong₂ inc c1≡c2 f≡g
insert-isInjective {a = fsuc a} {b = fsuc b} {f = inc c1 f} {g = inc c2 g} f''≡g'' =
  let c1≡c2 : c1 ≡ c2
      c1≡c2 = fsplice-isInjective (proj₁ (inc-isInjective f''≡g''))
      f≡g : f ≡ g
      f≡g = insert-isInjective (proj₂ (inc-isInjective f''≡g'')
          ∙ cong (λ ○ → insert a (antisplice ○ (fsuc b)) g) (sym c1≡c2))
  in cong₂ inc c1≡c2 f≡g

f∘f⁻¹≡id : ∀ {m} (f : Inj m m) → f ∘ʲ inv f ≡ idInj m
f∘f⁻¹≡id (nul 0) = refl
f∘f⁻¹≡id {m = suc m} (inc fzero f) =
  inc f0 f ∘ʲ inv (inc f0 f)
    ≡⟨ refl ⟩
  inc f0 f ∘ʲ insert f0 f0 (inv f)
    ≡⟨ refl ⟩
  inc f0 f ∘ʲ inc f0 (inv f)
    ≡⟨ refl ⟩
  inc (apply (inc f0 f) (apply (insert f0 f0 (inv f)) f0))
      (f ∘ʲ inv f)
    ≡⟨ refl ⟩
  inc (apply (inc f0 f) (apply (inc f0 (inv f)) f0))
      (f ∘ʲ inv f)
    ≡⟨ refl ⟩
  inc (apply (inc f0 f) f0)
      (f ∘ʲ inv f)
    ≡⟨ refl ⟩
  inc f0 (f ∘ʲ inv f)
    ≡⟨ cong (inc f0) (f∘f⁻¹≡id f) ⟩
  inc f0 (idInj m)
    ≡⟨ refl ⟩
  idInj (suc m) ▯
f∘f⁻¹≡id {m = suc m} (inc (fsuc b) (inc c f)) =
  inc (fsuc b) (inc c f) ∘ʲ inv (inc (fsuc b) (inc c f))
    ≡⟨ refl ⟩
  inc (fsuc b) (inc c f) ∘ʲ insert (fsuc b) f0 (inv (inc c f))
    ≡⟨ refl ⟩
  insert f0 (fsuc b) (inc c f) ∘ʲ insert (fsuc b) f0 (insert c f0 (inv f))
    ≡⟨ refl ⟩
  inc (fsuc b) (inc c f) ∘ʲ insert (fsuc b) f0 (insert c f0 (inv f))
    ≡⟨ {!!} ⟩
  idInj (suc m) ▯

inv-inc : (f : Inj m m) → (b : Fin (suc m)) → Inj (suc m) (suc m)
inv-inc f fzero = inc fzero f
inv-inc (inc b f) (fsuc a) = inc f0 (inv-inc f a)

isInjective : ∀ {A B : Type} (f : A → B) → Type
isInjective f = ∀ x y → f x ≡ f y → x ≡ y

isSurjective : ∀ {A B : Type} (f : A → B) → Type
isSurjective {A = A} f = ∀ y → Σ[ x ∈ A ] f x ≡ y

Inj-isInjective : ∀ {m n} → (f : Inj m n) → isInjective (apply f)
Inj-isInjective (inc b f) fzero fzero fx≡fy = refl
Inj-isInjective (inc b f) fzero (fsuc y) fx≡fy =
  absurd (fsplice≉b b (apply f y) (≡→≈ᶠ (sym fx≡fy)))
Inj-isInjective (inc b f) (fsuc x) fzero fx≡fy =
  absurd (fsplice≉b b (apply f x) (≡→≈ᶠ fx≡fy))
Inj-isInjective (inc b f) (fsuc x) (fsuc y) fx≡fy =
  cong fsuc (Inj-isInjective f x y (fsplice-isInjective fx≡fy))
