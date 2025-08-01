module VSet.Data.InductiveInj.Properties where

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
open import VSet.Data.InductiveInj.Base 
open import VSet.Data.InductiveInj.Order 
open import VSet.Data.InductiveInj.Inverse 
open import Cubical.Data.Maybe.Base hiding (elim)

private
  variable
    l l' m m' n n' : ℕ

splice-splice-antisplice 
  : ∀ {m} →  (b : Fin (suc (suc m))) → (c : Fin (suc m))
  → fsplice (fsplice b c) (antisplice c b)
  ≡ b
splice-splice-antisplice fzero fzero = refl
splice-splice-antisplice fzero (fsuc c) = refl
splice-splice-antisplice (fsuc b) fzero = refl
splice-splice-antisplice {m = suc m} (fsuc b) (fsuc c) =
  fsplice (fsplice (fsuc b) (fsuc c))
          (antisplice (fsuc c) (fsuc b))
    ≡⟨ refl ⟩
  fsplice (fsuc (fsplice b c))
          (fsuc (antisplice c b))
    ≡⟨ refl ⟩
  fsuc (fsplice (fsplice b c)
                (antisplice c b))
    ≡⟨ cong fsuc (splice-splice-antisplice b c) ⟩
  fsuc b ▯

apply-insert
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → (apply (insert a b f) a)
  ≡ b
apply-insert fzero fzero (nul 0) = refl
apply-insert fzero b f =
  apply (insert fzero b f) fzero ≡⟨ refl ⟩
  apply (inc b f) fzero ≡⟨ refl ⟩
  b ▯
apply-insert (fsuc a) b (inc c f) =
  apply (insert (fsuc a) b (inc c f)) (fsuc a)
    ≡⟨ refl ⟩
  apply (inc (fsplice b c) (insert a (antisplice c b) f)) (fsuc a)
    ≡⟨ refl ⟩
  fsplice (fsplice b c) (apply (insert a (antisplice c b) f) a)
    ≡⟨ cong (fsplice (fsplice b c))
            (apply-insert a (antisplice c b) f) ⟩
  fsplice (fsplice b c) (antisplice c b)
    ≡⟨ splice-splice-antisplice b c ⟩
  b ▯

apply-insert≡decRec
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → (x : Fin (suc m))
  → (apply (insert a b f) x)
  ≡ decRec (λ _ → b)
           (λ _ → fsplice b (apply f (antisplice {! a!} x)))
           (a ≡?ᶠ x)
apply-insert≡decRec a b f x = {!!}

apply-insert-≢-0
  : ∀ {m} → (a : Fin (suc m)) → (f : Inj m m)
  → (x : Fin (suc m)) → (a≢x : a ≢ x)
  → apply (insert a f0 f) x
  ≡ {!fsplice ? {!apply f ?!}!}
apply-insert-≢-0 fzero f fzero 0≢0 = absurd (0≢0 refl)
apply-insert-≢-0 fzero f (fsuc x) _ =
  apply (insert f0 f0 f) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc f0 f) (fsuc x)
    ≡⟨ refl ⟩
  {!fsplice f0 (apply f x)!} ▯
apply-insert-≢-0 (fsuc a) (inc c f) fzero a'≢0 =
  apply (insert (fsuc a) f0 (inc c f)) f0 
    ≡⟨ refl ⟩
  apply (inc (fsplice f0 c) (insert a (antisplice c f0) f)) f0 
    ≡⟨ refl ⟩
  fsplice f0 c
    ≡⟨ {!!} ⟩
  fsplice {!!} {!!} ▯
apply-insert-≢-0 (fsuc a) (inc c f) (fsuc x) a'≢x' with a ≟ᶠ x
... | flt a<x =
  apply (insert (fsuc a) f0 (inc c f)) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc (fsplice f0 c) (insert a (antisplice c f0) f)) (fsuc x)
    ≡⟨ refl ⟩
  fsplice (fsplice f0 c) (apply (insert a (antisplice c f0) f) x)
    ≡⟨ {!!} ⟩
  fsplice (fsuc c) (apply (insert a (antisplice c f0) f) x)
    ≡⟨ {!!} ⟩
  {!!} ▯
... | feq a≡x = absurd (≢cong fsuc a'≢x' a≡x)
... | fgt a>x = {!!}



inv-is-apply-inv : ∀ {m} → (f : Inj m m) → (y : Fin m)
                 → apply-inv f y ≡ just (apply (inv f) y)
inv-is-apply-inv {suc m} (inc b f) y with y ≡?ᶠ b
... | yes y≡b =
  apply-inv-rec f b y (yes y≡b) ≡⟨ refl ⟩
  just fzero ≡⟨ cong just (sym (apply-insert b f0 (inv f))) ⟩
  just (apply (insert b f0 (inv f)) b)
    ≡⟨ cong (λ ○ → just (apply (insert b f0 (inv f)) ○)) (sym y≡b) ⟩
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
-- inv-is-apply-inv (inc b f) y with y ≡? b
-- inv-is-apply-inv (inc b f) y | no y≢b =
--   apply-inv-rec f b y (no y≢b)
--     ≡⟨ {!!} ⟩
--   map-Maybe fsuc (apply-inv f {!funsplice b y y≢b!})
--     ≡⟨ cong (map-Maybe fsuc) (inv-is-apply-inv f {!funsplice b y y≢b!}) ⟩
--   map-Maybe fsuc (just (apply (inv f) {!funsplice b y y≢b!}))
--     ≡⟨ refl ⟩
--   just (fsuc (apply (inv f) {!funsplice b y y≢b!}))
--     ≡⟨ cong just (sym {!≢→apply-insert≡fsuc-apply b (inv f) y y≢b!}) ⟩
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

inc-isInjective : ∀ {m n} {b c : Fin (suc n)} {f g : Inj m n}
                → inc b f ≡ inc c g → (b ≡ c) × (f ≡ g)
inc-isInjective {b = b} {c} {f} {g} f'≡g'
  with f ≟ʲ g | b ≟ᶠ c
... | jlt f<g | _       = absurd {A = λ _ → (b ≡ c) × (f ≡ g)}
                                 (<ʲ→≢ (<j-suc f<g) f'≡g')
... | jeq f≡g | flt b<c = absurd {A = λ _ → (b ≡ c) × (f ≡ g)}
                                 (<ʲ→≢ (<j-fin f≡g b<c) f'≡g')
... | jeq f≡g | feq b≈c = (≈ᶠ→≡ b≈c , f≡g)
... | jeq f≡g | fgt c<b = absurd {A = λ _ → (b ≡ c) × (f ≡ g)}
                                 (<ʲ→≢ (<j-fin (sym f≡g) c<b) (sym f'≡g'))
... | jgt g<f | _       = absurd {A = λ _ → (b ≡ c) × (f ≡ g)}
                                 (<ʲ→≢ (<j-suc g<f) (sym f'≡g'))

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
      f≡g = insert-isInjective {!proj₂ (inc-isInjective f''≡g'')!}
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
  absurd (fsplice≢b b (apply f y) (sym fx≡fy))
Inj-isInjective (inc b f) (fsuc x) fzero fx≡fy =
  absurd (fsplice≢b b (apply f x) fx≡fy)
Inj-isInjective (inc b f) (fsuc x) (fsuc y) fx≡fy =
  cong fsuc (Inj-isInjective f x y (fsplice-isInjective fx≡fy))

Injmm-isSurjective-suc
  : ∀ {m} → (b : Fin (suc m)) (f : Inj m m)
  → (y : Fin (suc m)) → Trichotomyᶠ b y
  → Σ[ x ∈ Fin (suc m) ] (apply (inc b f) x) ≡ y
Injmm-isSurjective : ∀ {m} → (f : Inj m m) → isSurjective (apply f)

Injmm-isSurjective-suc {m = zero} fzero f fzero tr = fzero , refl
Injmm-isSurjective-suc {m = suc m} fzero f (fsuc y) (flt _) =
  let a , fa≡y = Injmm-isSurjective f y 
  in (fsuc a) , (cong fsuc fa≡y)
Injmm-isSurjective-suc {m = suc m} (fsuc b) f (fsuc y) (flt b<y) =
  let a , fa≡y = Injmm-isSurjective f y 
  in (fsuc a)
   , ≤→fsplice≡suc (apply f a) (fsuc b)
       (weaken<-pred (subst (λ ○ → fsuc b <ᶠ fsuc ○) (sym fa≡y) b<y)) ∙ cong fsuc fa≡y
Injmm-isSurjective-suc {m = suc m} b f y (feq b≡y) = fzero , b≡y
Injmm-isSurjective-suc {m = suc m} (fsuc b) f y (fgt b>y) =
  let a , fa≡y = Injmm-isSurjective f (fin-restrict y b>y) 
  in finj a , {!!}
    -- (apply (inc (fsuc b) f) (finj a) ≡⟨ {!!} ⟩
    -- {!!} ≡⟨ {!!} ⟩
    -- y ▯)
Injmm-isSurjective-suc {m = suc m} (fsuc b) f (fsuc y) (fgt b>y) = {!!}

-- Injmm-isSurjective-suc {m = suc m} (fsuc b) f y (fgt b>y) with inspect' (antisplice b y)
-- ... | fzero , antisplice≡0 =
--   let a , fa≡antisplice = Injmm-isSurjective f (antisplice b y)
--   in fsuc a , (
--     apply (inc (fsuc b) f) (fsuc a)
--       ≡⟨ refl ⟩
--     fsplice (fsuc b) (apply f a)
--       ≡⟨ cong (fsplice (fsuc b)) fa≡antisplice ⟩
--     fsplice (fsuc b) (antisplice b y)
--       ≡⟨ cong (fsplice (fsuc b)) antisplice≡0 ⟩
--     fsplice (fsuc b) fzero
--       ≡⟨ {!!} ⟩
--     y ▯) 
-- ... | fsuc w , w'≡antisplice = {!!}
--   -- let a , fa≡antisplice = Injmm-isSurjective f (antisplice b y)
--   -- in fsuc a , (
--   --   apply (inc (fsuc b) f) (fsuc a)
--   --     ≡⟨ refl ⟩
--   --   fsplice (fsuc b) (apply f a)
--   --     ≡⟨ cong (fsplice (fsuc b)) fa≡antisplice ⟩
--   --   fsplice (fsuc b) (antisplice b y)
--   --     ≡⟨ {!!} ⟩
--   --   y ▯) 
--   -- in fsuc a , subst (λ ○ → fsplice (fsuc b) ○ ≡ y) (sym fa≡y)
--   --                   (>→fsplice≡id (funinj y) (fsuc b) {!!} ∙ {!!})

Injmm-isSurjective {suc zero} (inc fzero (nul 0)) fzero = fzero , refl
Injmm-isSurjective {suc (suc m)} (inc b f) fzero with b ≟ᶠ fzero
... | flt ()
... | feq b≡0 = fzero , b≡0
... | fgt b>0 =
  let x , fx≡0 = Injmm-isSurjective f fzero
      w : Σ[ x'' ∈ Fin (suc (suc m)) ] apply (inc b f) x'' ≡ fzero
      w = case x of
        λ{ fzero → {!!}
         ; (fsuc x') → {!!} }
  in {!!} , {!!}
Injmm-isSurjective {suc (suc m)} (inc b f) y with b ≟ᶠ y
... | flt b<y =
  let x , fx≡py = Injmm-isSurjective f (pred y)
  in fsuc x , (
      apply (inc b f) (fsuc x) ≡⟨ refl ⟩
      fsplice b (apply f x) ≡⟨ cong (fsplice b) fx≡py ⟩
      fsplice b (pred y) ≡⟨ ≤→fsplice≡suc (pred y) b (weaken<-pred {!b<y!}) ⟩
      fsuc (pred y) ≡⟨ {!≤→fsplice≡suc!} ⟩
      y ▯)
... | feq b≡y = fzero , b≡y
... | fgt b>y = {!!}



-- Injmm-isSurjective : ∀ {m} → (f : Inj m m) → isSurjective (apply f)
-- Injmm-isSurjective (inc fzero f) fzero = fzero , refl
-- Injmm-isSurjective (inc fzero f) (fsuc y) =
--   let x , fx≡y = Injmm-isSurjective f y
--   in (fsplice fzero x) , cong fsuc fx≡y
-- Injmm-isSurjective {m = suc (suc m)} (inc (fsuc b) f) fzero =
--   let x , fx≡y = Injmm-isSurjective f fzero
--   in (fsplice (fsuc b) x) , {!cong fsuc fx≡y!}
-- Injmm-isSurjective {m = suc m} (inc (fsuc b) f) (fsuc y) =
--   let x , fx≡y = Injmm-isSurjective f y
--   in (fsplice fzero x) , {!cong fsuc fx≡y!}
