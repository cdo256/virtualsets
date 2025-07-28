module VSet.Data.InductiveInj.Properties where

open import VSet.Prelude hiding (_∘_)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.InductiveInj.Base 
open import VSet.Data.InductiveInj.Order 
open import Cubical.Data.Maybe.Base

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

Surjective : (f : Inj m n) → Type
Surjective {m = m} {n = n} f = ∀ (b : Fin n) → Σ[ a ∈ Fin m ] apply f a ≡ b

apply-inv : {m n : ℕ} → (f : Inj m n) → (b : Fin n) → Maybe (Fin m)
apply-inv {zero} {n} (nul n) b = nothing
apply-inv {suc m} {suc n} (inc fzero f) fzero = just fzero
-- ((1 2 3 0)⁻¹ 0) = fsuc ((1 2 0)⁻¹ 0)
apply-inv {suc m} {suc (suc n)} (inc (fsuc c) f) fzero =
  map-Maybe fsuc $ apply-inv f fzero
-- ((0 3 2 1)⁻¹ 2) = fsuc ((2 1 0)⁻¹ 1)
-- ((1 2 3 0)⁻¹ 2) = fsuc ((1 2 0)⁻¹ 1)
apply-inv {suc m} {suc n} (inc c f) (fsuc b) =
  map-Maybe fsuc $ apply-inv f b

insert : ∀ {m n} → (f : Inj m n) → (a : Fin (suc m)) → (b : Fin (suc n))
       → Inj (suc m) (suc n)
insert f fzero b = inc b f
insert (inc {m} {n} c f) (fsuc a) fzero =
  inc (fsuc c) (insert f a fzero)
insert (inc {m} {n} c f) (fsuc a) (fsuc b) with b ≤?ᶠ c
... | fle b≤c = inc (fsuc c) (insert f a b)
... | fgt c>b = inc (finj c) (insert f a b)

insert-rev : ∀ {m n} → (f : Inj m n) → (a : Fin (suc m)) → Inj (suc m) (suc n)
insert-rev (nul _) a = inc fzero (nul _)
-- (ins (0 2 1 3) 0) = (0 1 3 2 4)
-- (ins (1 2 3 0) 0) = (0 2 3 4 1)
insert-rev f fzero = inc fzero f
-- (ins (0 2 1 3) 1) = (1 0 3 2 4)
-- (ins (0 2 1 3) 2) = (1 3 0 2 4)
insert-rev (inc b f) (fsuc a) =
  let g = insert-rev f a
  in inc (fsuc b) g

inv : ∀ {m} → (f : Inj m m) → Inj m m
inv {zero} (nul zero) = nul zero
inv {suc m} (inc c f) = insert-rev (inv f) c

test3 = inv (cycle-r 3)
test4 = inv (cycle-l 3)

-- Not sure if this is the simplest way to do it.
_∘_ : ∀ {l m n} → (g : Inj m n) → (f : Inj l m) → Inj l n 
g ∘ nul _ = nul _
inc c g ∘ inc b f =
  let h'0 = apply (inc c g) (apply (inc b f) fzero)
  in inc h'0 (g ∘ f)

+suc : ∀ {m n} → m + suc n ≡ suc (m + n)
+suc {zero}    {n} = refl
+suc {suc m} {n} = cong suc (+-suc m n)

shift' : ∀ {m n} → (l : ℕ) → (f : Inj m n) → Inj m (l + n)
shift' l (nul _) = nul _
shift' {m = m} {n = suc n} l (inc b f) =
  subst (Inj m) (sym +suc) $
    inc (subst Fin +suc (fshift l b)) (shift' l f)

shift : ∀ {m n} → (l : ℕ) → (f : Inj m n) → Inj m (l + n)
shift l (nul _) = nul _
shift {m = m} {n = suc n} l (inc b f) =
  subst (Inj m) (sym +suc) $
    inc (subst Fin +suc (fshift l b)) (shift l f)

tensor : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
tensor (nul m') g = shift m' g
tensor (inc b f) (nul n') =
  inc (finject n' b) $ tensor f (nul n')
tensor (inc b f) (inc b' g) =
  inc (finject (suc _) b) $ tensor f (inc b' g)

-- tensor : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
-- tensor (nul m') g = shift m' g
-- tensor (inc b f) (nul n') =
--   inc (finject n' b) $ tensor f (nul n')
-- tensor (inc b f) (inc b' g) =
--   inc (finject (suc _) b) $ tensor f (inc b' g)

_⊕_ : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
f ⊕ g = tensor f g

test5 : Inj 5 6
test5 = nul 1 ⊕ cycle-l 4 
test5' = to-list test5

test6 : Inj 1 2
test6 = nul 1 ⊕ idInj 1 
test6' = to-list test6



-- Injmm-suc : ∀ {m} (b c : Fin (suc (suc m)))
--           → (f : Inj (suc m) (suc m))
--           → (Σ[ a ∈ Fin (suc (suc m)) ] apply (inc c f) a ≡ b)
--           → Σ[ a' ∈ Fin (suc m) ] apply f a' ≡ {!!}
-- Injmm-suc fzero fzero f (fzero , f'a≡b) = fzero , refl
-- Injmm-suc fzero fzero f (fsuc a , f'a≡b) =
--   let a' = {!!}
--   in {!!} , {!!}
-- Injmm-suc fzero (fsuc c) f (fzero , f'a≡b) = {!!}
-- Injmm-suc fzero (fsuc c) f (fsuc a , f'a≡b) = {!!}
-- Injmm-suc (fsuc b) fzero f (fzero , f'a≡b) = {!!}
-- Injmm-suc (fsuc b) fzero f (fsuc a , f'a≡b) = {!!}
-- Injmm-suc (fsuc b) (fsuc c) f (fzero , f'a≡b) = {!!}
-- Injmm-suc (fsuc b) (fsuc c) f (fsuc a , f'a≡b) = {!!}

<ʲ→≢ : ∀ {m n} → {f g : Inj m n}
     → f <ʲ g → f ≢ g
<ʲ→≢ {f = f} f<g f≡g = ¬f<f (subst (f <ʲ_) (sym f≡g) f<g)

discreteInj : Discrete (Inj m n)
discreteInj f g with f ≟ʲ g
... | jlt f<g = no (<ʲ→≢ f<g)
... | jeq f≡g = yes f≡g
... | jgt g<f = no (≢sym (<ʲ→≢ g<f))

isSetInj : isSet (Inj m n)
isSetInj = Discrete→isSet discreteInj

f-f⁻¹-b≡b : ∀ {m} (f : Inj m m) → ∀ b → apply f (apply (inv f) b) ≡ b
f-f⁻¹-b≡b (inc fzero (nul 0)) fzero = refl
f-f⁻¹-b≡b {m = suc m} (inc fzero (inc d f)) fzero =
  apply (inc fzero (inc d f))
   (apply (inv (inc fzero (inc d f))) fzero)
    ≡⟨ {!!} ⟩
  apply (inc fzero (inc d f))
   (apply {!inv (inc fzero (inc d f))!} fzero)
    ≡⟨ {!!} ⟩
  fzero ▯
f-f⁻¹-b≡b (inc fzero f) (fsuc b) =
  {!!}
    ≡⟨ {!!} ⟩
  {!!} ▯
f-f⁻¹-b≡b (inc (fsuc c) f) fzero =
  {!!}
    ≡⟨ {!!} ⟩
  {!!} ▯
f-f⁻¹-b≡b (inc (fsuc c) f) (fsuc b) =
  {!!}
    ≡⟨ {!!} ⟩
  {!!} ▯

f∘f⁻¹≡id : ∀ {m} (f : Inj m m) → f ∘ inv f ≡ idInj m
f∘f⁻¹≡id (nul 0) = refl
f∘f⁻¹≡id {m = suc m} (inc fzero f) =
  inc f0 f ∘ inv (inc f0 f)
    ≡⟨ refl ⟩
  inc f0 f ∘ insert-rev (inv f) f0
    ≡⟨ {!!} ⟩
  inc f0 f ∘ insert-rev (inv f) f0
    ≡⟨ {!!} ⟩
  inc (apply (inc f0 f) (apply (insert-rev (inv f) f0) f0))
      (f ∘ {!insert-rev {!inv f!} {!f0!}!})
    ≡⟨ {!!} ⟩
  idInj (suc m) ▯
f∘f⁻¹≡id (inc (fsuc b) f) = {!!}

Injmm→Surjective : ∀ {m} → (f : Inj m m) → Surjective f
Injmm→Surjective {suc m} f b =
  -- Σ[ a ∈ Fin m ] apply f a ≡ b
  let a = apply (inv f) b
  in a , {!!}


-- Injmm→Surjective : ∀ {m} → (f : Inj m m) → Surjective f
-- Injmm→Surjective {suc m} (inc fzero f) fzero = fzero , refl
-- Injmm→Surjective {suc m} (inc fzero f) (fsuc b) =
--   let a , fa≡b = Injmm→Surjective f b
--   in fsuc a , cong fsuc fa≡b
-- Injmm→Surjective {suc m} (inc (fsuc c) f) fzero =
--   let a , fa≡b = Injmm→Surjective f {!fzero!}
--   in fsuc a , {!!}
-- Injmm→Surjective {suc m} (inc (fsuc c) f) (fsuc b) =
--   let a , fa≡b = Injmm→Surjective f b
--   in fsuc a , {!!}


-- Injmm→Surjective : {m : ℕ} → (f : Inj m m) → Surjective f
-- Injmm→Surjective {m = suc m} (inc fzero f) fzero = fzero , refl
-- Injmm→Surjective {m = suc m} (inc fzero f) (fsuc b) =
--   let
--     d : Fin (suc m)
--     d = fsplice fzero b
--     a , fa≡b = Injmm→Surjective f b
--     eq' = 
--       apply (inc fzero f) (fsuc a)
--         ≡⟨ refl ⟩
--       fsplice fzero (apply f a) 
--         ≡⟨ refl ⟩
--       fsuc (apply f a) 
--         ≡⟨ cong fsuc fa≡b ⟩
--       fsuc b ▯
--   in fsuc a , eq' 
-- Injmm→Surjective {m = suc (suc m)} (inc (fsuc c) f) fzero =
--   let
--     a , fa≡0 = Injmm→Surjective f fzero 
--     eq' : apply (inc (fsuc c) f) (fsuc a) ≡ fzero
--     eq' = 
--       apply (inc (fsuc c) f) (fsuc a)
--         ≡⟨ refl ⟩
--       fsplice (fsuc c) (apply f a)
--         ≡⟨ cong (fsplice (fsuc c)) fa≡0 ⟩
--       fsplice (fsuc c) fzero 
--         ≡⟨ refl ⟩
--       fzero ▯
--   in fsuc a , eq' 
-- -- Injmm→Surjective {m = suc (suc m)} (inc (fsuc c) f) (fsuc (fsuc b)) with Injmm→Surjective f (fsuc b)
-- -- ... | fzero , f0≡sb =
-- --   let
-- --     eq' : apply (inc (fsuc c) f) (fsuc fzero) ≡ fsuc (fsuc b)
-- --     eq' = 
-- --       apply (inc (fsuc c) f) (fsuc fzero)
-- --         ≡⟨ refl ⟩
-- --       fsplice (fsuc c) (apply f fzero) 
-- --         ≡⟨ cong (fsplice (fsuc c)) f0≡sb ⟩
-- --       fsplice (fsuc c) (fsuc b)
-- --         ≡⟨ refl ⟩
-- --       fsuc (fsplice c b)
-- --         ≡⟨ {!!} ⟩
-- --       fsuc (fsuc b) ▯
-- --   in fsuc fzero , eq'

-- -- ... | fsuc a , fa≡b = {!!}

-- Injmm→Surjective {m = suc (suc m)} (inc (fsuc c) f) (fsuc b)
--   with Injmm→Surjective f b
-- ... | fzero , f0≡b =
--   let
--     eq' : apply (inc (fsuc c) f) (fsuc fzero) ≡ fsuc b
--     eq' = 
--       apply (inc (fsuc c) f) (fsuc fzero)
--         ≡⟨ refl ⟩
--       fsplice (fsuc c) (apply f fzero) 
--         ≡⟨ cong (fsplice (fsuc c)) f0≡b ⟩
--       fsplice (fsuc c) b
--         ≡⟨ {!!} ⟩
--       fsuc b ▯
--   in fsuc fzero , eq'

-- ... | fsuc a , fa≡b = {!!}

inv-inc-insert : (f : Inj m n) (b : Fin (suc m)) → Inj (suc n) (suc m)
inv-inc-insert (nul _) fzero = inc fzero {!!}
inv-inc-insert (inc b f) fzero = inc fzero {!!}
inv-inc-insert f (fsuc b) = {!!}

inv-inc : (f : Inj m m) → (b : Fin (suc m)) → Inj (suc m) (suc m)
inv-inc f fzero = inc fzero f
inv-inc (inc b f) (fsuc a) = {!!}

-- inv : (f : Inj m m) → Inj m m
-- inv (nul 0) = nul 0
-- inv (inc b f) =
--   let g = inv f
--   in {!inv-inc g b!}

equalInjIsIso : (f : Inj m m) → isIso (apply f)
