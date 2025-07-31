module VSet.Data.InductiveInj.Properties where

open import VSet.Prelude hiding (_∘_)
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
open import Cubical.Data.Maybe.Base hiding (elim)

private
  variable
    l l' m m' n n' : ℕ

inc-congP : ∀ {m m' n n'}
          → {b : Fin (suc n)} {b' : Fin (suc n')}
          → {f : Inj m n} {f' : Inj m' n'}
          → (meq : m ≡ m') (neq : n ≡ n') (beq : (λ i → Fin (suc (neq i))) [ b ≡ b' ])
          → (feq' : (λ i → Inj (meq i) (neq i)) [ f ≡ f' ])
          → (λ i → cong₂ Injsuc meq neq i) [ (inc {m} {n} b f) ≡ inc {m'} {n'} b' f' ]
inc-congP meq neq beq feq' i =
  inc {meq i} {neq i} (beq i) (feq' i)

inc-cong : ∀ {m n} (b b' : Fin (suc n))
         → (f f' : Inj m n)
         → (beq : b ≡ b') → (feq' : f ≡ f')
         → inc b f ≡ inc b' f'
inc-cong b b' f f' beq feq' = cong₂ inc beq feq'

apply-inv-rec : {m n : ℕ} → (f : Inj m n) → (b y : Fin (suc n)) → Trichotomyᶠ y b → Maybe (Fin (suc m))
apply-inv : {m n : ℕ} → (f : Inj m n) → (y : Fin n) → Maybe (Fin m)

apply-inv-rec f b y (flt y<b) = map-Maybe fsuc (apply-inv f (fin-restrict y y<b))
apply-inv-rec f b y (feq y≡b) = just fzero
apply-inv-rec f b (fsuc y) (fgt y>b) = map-Maybe fsuc (apply-inv f y)

apply-inv {zero} {n} (nul n) y = nothing
apply-inv (inc b f) y = apply-inv-rec f b y (y ≟ᶠ b)

insert : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
       → (f : Inj m n) → Inj (suc m) (suc n)
insert fzero b f = inc b f
insert (fsuc a) b (inc c f) =
  inc (fsplice b c) (insert a (antisplice c b) f)

-- insert : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
--        → (f : Inj m n) → Inj (suc m) (suc n)
-- insert fzero b f =
--   inc b f
-- insert (fsuc a) b (inc c f) with b ≟ᶠ finj c
-- ... | flt b<c = inc (fsuc c) (insert a (fin-restrict b b<c) f)
-- ... | feq b≡c = inc (fsuc c) (insert a c f) -- using c≡b
-- ... | fgt b>c = inc (finj c) (insert a (pred b) f)


-- insert (fsuc a) fzero (inc c f) = inc (fsuc c) (insert a fzero f)
-- insert (fsuc a) (fsuc b) (inc c f) = inc (fsplice (fsuc b) c) (insert a b f)

inv : ∀ {m} → (f : Inj m m) → Inj m m
inv {zero} (nul zero) = nul zero
inv {suc m} (inc c f) = insert c fzero (inv f)

<→apply-insert≡fsuc-apply
  : ∀ {m} → (a : Fin (suc m)) → (f : Inj m m)
  → (y : Fin (suc m)) → (y<a : y <ᶠ a)
  → (apply (insert a f0 f) y)
  ≡ (fsuc (apply f (fin-restrict y y<a)))
<→apply-insert≡fsuc-apply (fsuc a) (inc c f) fzero <fzero =
  cong fsuc (
    apply (inc c f) (fin-restrict f0 (<fzero {b = a}))
      ≡⟨ refl ⟩
    apply (inc c f) fzero
      ≡⟨ refl ⟩
    c ▯)
<→apply-insert≡fsuc-apply (fsuc a) (inc c f) (fsuc y) (<fsuc y<a) =
  apply (insert (fsuc a) f0 (inc c f)) (fsuc y)
    ≡⟨ refl ⟩
  apply (inc (fsuc c) (insert a fzero f)) (fsuc y)
    ≡⟨ refl ⟩
  fsplice (fsuc c) (apply (insert a fzero f) y)
    ≡⟨ cong (fsplice (fsuc c)) (<→apply-insert≡fsuc-apply a f y y<a) ⟩
  fsplice (fsuc c) (fsuc (apply f (fin-restrict y y<a)))
    ≡⟨ refl ⟩
  fsuc (apply (inc c f) (fin-restrict (fsuc y) (<fsuc y<a))) ▯

fsplice-fsplice-fsuc
  : ∀ {m} → (b c : Fin (suc m)) → (f : Inj m m)
  → fsplice (fsplice (fsuc b) c) b 
  ≡ fsuc b
fsplice-fsplice-fsuc fzero fzero f = refl
fsplice-fsplice-fsuc fzero (fsuc c) f = {!!}
fsplice-fsplice-fsuc (fsuc b) c f = {!!}

  -- fsplice (fsplice (fsuc b) c) b 
  --   ≡⟨ {!!} ⟩
  -- fsuc b ▯


apply-insert
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → apply (insert a b f) a
  ≡ b
apply-insert fzero fzero (nul 0) = refl
apply-insert fzero b (inc c f) = refl
apply-insert (fsuc a) fzero (inc c f) =
  apply (insert (fsuc a) f0 (inc c f)) (fsuc a)
    ≡⟨ refl ⟩
  apply (inc (fsuc c) (insert a f0 f)) (fsuc a)
    ≡⟨ refl ⟩
  fsplice (fsuc c) (apply (insert a f0 f) a) 
    ≡⟨ cong (fsplice (fsuc c)) (apply-insert a f0 f) ⟩
  fsplice (fsuc c) f0 
    ≡⟨ refl ⟩
  f0 ▯
apply-insert (fsuc a) (fsuc b) (inc c f) =
  apply (insert (fsuc a) (fsuc b) (inc c f)) (fsuc a)
    ≡⟨ {!!} ⟩
  apply (inc (fsplice (fsuc b) c) (insert a b f)) (fsuc a)
    ≡⟨ refl ⟩
  fsplice (fsplice (fsuc b) c) (apply (insert a b f) a) 
    ≡⟨ cong (fsplice (fsplice (fsuc b) c)) (apply-insert a b f) ⟩
  fsplice (fsplice (fsuc b) c) b 
    ≡⟨ {!!} ⟩
  fsuc b ▯

≡→apply-insert≡fsuc-apply
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → (y : Fin (suc m)) → (y≡a : y ≡ a)
  → (apply (insert a b f) y)
  ≡ b
≡→apply-insert≡fsuc-apply fzero fzero (nul .0) fzero _ = refl
≡→apply-insert≡fsuc-apply a b (inc c f) y y≡a = {!!}
-- ≡→apply-insert≡fsuc-apply a b (inc c f) y y≡b = {!!}
  -- {!!}
  --   ≡⟨ ? ⟩
  -- ? ▯

inv-is-apply-inv : ∀ {m} → (f : Inj m m) → (y : Fin m)
                 → apply-inv f y ≡ just (apply (inv f) y)
inv-is-apply-inv (inc b f) y with y ≟ᶠ b
inv-is-apply-inv (inc b f) y | flt y<b =
  apply-inv-rec f b y (flt y<b)
    ≡⟨ refl ⟩
  map-Maybe fsuc (apply-inv f (fin-restrict y y<b))
    ≡⟨ cong (map-Maybe fsuc) (inv-is-apply-inv f (fin-restrict y y<b)) ⟩
  map-Maybe fsuc (just (apply (inv f) (fin-restrict y y<b)))
    ≡⟨ refl ⟩
  just (fsuc (apply (inv f) (fin-restrict y y<b)))
    ≡⟨ cong just (sym (<→apply-insert≡fsuc-apply b (inv f) y y<b)) ⟩
  just (apply (insert b f0 (inv f)) y) ▯
inv-is-apply-inv (inc b f) y | feq y≡b =
  apply-inv-rec f b y (feq y≡b)
    ≡⟨ refl ⟩
  just f0
    ≡⟨ cong just {!!} ⟩
  just (apply (insert b f0 (inv f)) y) ▯
inv-is-apply-inv (inc b f) y | fgt y>b = {!!}

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


-- Not sure if this is the simplest way to do it.
_∘_ : ∀ {l m n} → (g : Inj m n) → (f : Inj l m) → Inj l n 
g ∘ nul _ = nul _
inc c g ∘ inc b f =
  let h'0 = apply (inc c g) (apply (inc b f) fzero)
  in inc h'0 (g ∘ f)

+suc : ∀ {m n} → m + suc n ≡ suc (m + n)
+suc {zero} {n} = refl
+suc {suc m} {n} = cong suc (+-suc m n)

shift1 : ∀ {m n} → (f : Inj m n) → Inj m (suc n)
shift1 (nul _) = nul _
shift1 (inc b f) =
  inc (fsuc b) (shift1 f)

shift : ∀ {m n} → (l : ℕ) → (f : Inj m n) → Inj m (l + n)
shift zero f = f
shift (suc l) f = shift1 (shift l f) 

tensor : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
tensor (nul m') g =
  shift m' g
tensor (inc b f) (nul n') =
  inc (finject n' b) (tensor f (nul n'))
tensor (inc b f) (inc b' g) =
  inc (finject (suc _) b) (tensor f (inc b' g))

_⊕_ : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
f ⊕ g = tensor f g

<ʲ→≢ : ∀ {m n} → {f g : Inj m n}
     → f <ʲ g → f ≢ g
<ʲ→≢ {f = f} f<g f≡g = ¬f<f (subst (f <ʲ_) (sym f≡g) f<g)

≡→≮ʲ : ∀ {m n} → {f g : Inj m n}
     → f ≡ g → ¬ f <ʲ g
≡→≮ʲ f≡g f<g = <ʲ→≢ f<g f≡g

≮ʲ→≡ : ∀ {m n} → {f g : Inj m n}
     → ¬ f <ʲ g → ¬ g <ʲ f → f ≡ g
≮ʲ→≡ {f = nul _} {g = nul _} _ _ = refl
≮ʲ→≡ {f = inc b f} {g = inc c g} f'≮g' g'≮f' with inc b f ≟ʲ inc c g
... | jlt f'<g' = absurd (f'≮g' f'<g')
... | jeq f'≡g' = f'≡g'
... | jgt g'<f' = absurd (g'≮f' g'<f')

discreteInj : Discrete (Inj m n)
discreteInj f g with f ≟ʲ g
... | jlt f<g = no (<ʲ→≢ f<g)
... | jeq f≡g = yes f≡g
... | jgt g<f = no (≢sym (<ʲ→≢ g<f))

isSetInj : isSet (Inj m n)
isSetInj = Discrete→isSet discreteInj

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
... | jeq f≡g | feq b≡c = (b≡c , f≡g)
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
  → insert b f0 g ∘ insert f0 b f ≡ insert f0 f0 (g ∘ f)
insert-comp fzero f g = refl
insert-comp (fsuc b) f (inc c g) =
  insert (fsuc b) f0 (inc c g) ∘ insert f0 (fsuc b) f
    ≡⟨ refl ⟩
  insert (fsuc b) f0 (inc c g) ∘ inc (fsuc b) f
    ≡⟨ {!!} ⟩
  insert f0 f0 (inc c g ∘ f) ▯

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

f∘f⁻¹≡id : ∀ {m} (f : Inj m m) → f ∘ inv f ≡ idInj m
f∘f⁻¹≡id (nul 0) = refl
f∘f⁻¹≡id {m = suc m} (inc fzero f) =
  inc f0 f ∘ inv (inc f0 f)
    ≡⟨ refl ⟩
  inc f0 f ∘ insert f0 f0 (inv f)
    ≡⟨ refl ⟩
  inc f0 f ∘ inc f0 (inv f)
    ≡⟨ refl ⟩
  inc (apply (inc f0 f) (apply (insert f0 f0 (inv f)) f0))
      (f ∘ inv f)
    ≡⟨ refl ⟩
  inc (apply (inc f0 f) (apply (inc f0 (inv f)) f0))
      (f ∘ inv f)
    ≡⟨ refl ⟩
  inc (apply (inc f0 f) f0)
      (f ∘ inv f)
    ≡⟨ refl ⟩
  inc f0 (f ∘ inv f)
    ≡⟨ cong (inc f0) (f∘f⁻¹≡id f) ⟩
  inc f0 (idInj m)
    ≡⟨ refl ⟩
  idInj (suc m) ▯
f∘f⁻¹≡id {m = suc m} (inc (fsuc b) (inc c f)) =
  inc (fsuc b) (inc c f) ∘ inv (inc (fsuc b) (inc c f))
    ≡⟨ refl ⟩
  inc (fsuc b) (inc c f) ∘ insert (fsuc b) f0 (inv (inc c f))
    ≡⟨ refl ⟩
  insert f0 (fsuc b) (inc c f) ∘ insert (fsuc b) f0 (insert c f0 (inv f))
    ≡⟨ refl ⟩
  inc (fsuc b) (inc c f) ∘ insert (fsuc b) f0 (insert c f0 (inv f))
    ≡⟨ {!!} ⟩
  idInj (suc m) ▯

inv-inc : (f : Inj m m) → (b : Fin (suc m)) → Inj (suc m) (suc m)
inv-inc f fzero = inc fzero f
inv-inc (inc b f) (fsuc a) = inc f0 (inv-inc f a)

-- inv : (f : Inj m m) → Inj m m
-- inv (nul 0) = nul 0
-- inv (inc b f) =
--   let g = inv f
--   in {!inv-inc g b!}

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
