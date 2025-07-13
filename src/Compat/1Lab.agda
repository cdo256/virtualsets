module Compat.1Lab where

open import Cubical.Foundations.Prelude as Cubical
  renaming ( hcomp to cubical-hcomp
           ; hfill to cubical-hfill
           )

∂ : I → I
∂ i  = i ∨ ~ i

-- compat-Square
--   : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
--   → (p : a00 ≡ a01) (q : a00 ≡ a10) (s : a01 ≡ a11) (r : a10 ≡ a11)
--   → Type ℓ
-- compat-Square p q s r = Square q s p r

-- 1lab-Square
--   : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
--   → (p : a00 ≡ a01) (q : a00 ≡ a10) (s : a01 ≡ a11) (r : a10 ≡ a11)
--   → Type ℓ
-- 1lab-Square p q s r = PathP (λ i → p i ≡ r i) q s

-- primHComp  : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A


compat-hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
compat-hcomp {A = A} φ u =
  cubical-hcomp sys (u i0 1=1) where
    sys : ∀ j → Partial φ A
    sys j (φ = i1) = u j 1=1

1lab-hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
1lab-hcomp {A = A} φ u = cubical-hcomp sys (u i0 1=1) where
  sys : ∀ j → Partial φ A
  sys j (φ = i1) = u j 1=1

1lab-hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
1lab-hfill φ i u = 1lab-hcomp (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1

compat-hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
compat-hfill {A = A} φ i u = hcomp where
  f : (j : I) → Partial (φ ∨ ~ i ∨ ~ j) A
  f j (φ = i1) = u (i ∧ j) 1=1
  f j (i = i0) = u i0 1=1
  f j (j = i0) = u i0 1=1

  sys : ∀ j → Partial (φ ∨ ~ i) A
  sys j (φ = i1) = f j 1=1
  sys j (i = i0) = f j 1=1

  hcomp : A
  hcomp  = cubical-hcomp sys (u i0 1=1)

-- cong-∙∙ : ∀ {B : Type ℓ} (f : A → B) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
--           → cong f (p ∙∙ q ∙∙ r) ≡ (cong f p) ∙∙ (cong f q) ∙∙ (cong f r)
-- cong-∙∙ f p q r j i = cong-∙∙-filler f p q r i1 j i

-- cong-∙ : ∀ {B : Type ℓ} (f : A → B) (p : x ≡ y) (q : y ≡ z)
--          → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
-- cong-∙ f p q = cong-∙∙ f refl p q

--- agda-cubical
-- hfill : {A : Type ℓ}
--         {φ : I}
--         (u : ∀ i → Partial φ A)
--         (u0 : A [ φ ↦ u i0 ])
--         -----------------------
--         (i : I) → A
-- hfill {φ = φ} u u0 i =
--   hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
--                  ; (i = i0) → outS u0 })
--         (outS u0)

1lab-∙∙-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → Square q (p ∙∙ q ∙∙ r) (sym p) r
1lab-∙∙-filler p q r i j = compat-hfill (∂ j) i λ where
  k (j = i0) → p (~ k)
  k (j = i1) → r k
  k (k = i0) → q j

compat-∙∙-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → Square q (p ∙∙ q ∙∙ r) (sym p) r
compat-∙∙-filler {A = A} p q r i j = out where
  u : (k : I) → Partial (~ j ∨ j ∨ ~ k) A
  u k (j = i0) = p (~ k)
  u k (j = i1) = r k
  u k (k = i0) = q j

  f : (l : I) → Partial (j ∨ ~ j ∨ ~ i ∨ ~ l) A
  f l (j = i1) = u (i ∧ l) 1=1
  f l (j = i0) = u (i ∧ l) 1=1
  f l (i = i0) = u i0 1=1
  f l (l = i0) = u i0 1=1

  sys : ∀ l → Partial (j ∨ ~ j ∨ ~ i) A
  sys l (j = i1) = f l 1=1
  sys l (j = i0) = f l 1=1
  sys l (i = i0) = f l 1=1

  out : A
  out = cubical-hcomp sys (u i0 1=1)

module DoubleCompUnique {ℓ : Level} {A : Type ℓ}
    {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    (α' β' : Σ[ s ∈ w ≡ z ] Square q s (sym p) r) where

  α = fst α'
  α-fill = snd α'

  β = fst β'
  β-fill = snd β'

  cube : (i j : I) → p (~ j) ≡ r j
  cube i j k = compat-hfill (∂ i ∨ ∂ k) j λ where
    l (i = i0) → α-fill l k
    l (i = i1) → β-fill l k
    l (k = i0) → p (~ l)
    l (k = i1) → r l
    l (l = i0) → q k

  square : α ≡ β
  square i j = cube i i1 j
  
  ∙∙-unique : α' ≡ β'
  ∙∙-unique = λ i → (λ j → square i j) , (λ j k → cube i j k)

open DoubleCompUnique using (∙∙-unique)

{-

∙∙-contract : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → (β : Σ[ s ∈ (w ≡ z) ] Square q s (sym p) r)
            → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ≡ β
∙∙-contract p q r β = ∙∙-unique p q r _ β

∙∙-unique'
  : {ℓ : Level} {A : Type ℓ}
  → {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
  → (β : Square q s (sym p) r)
  → s ≡ p ∙∙ q ∙∙ r
∙∙-unique' β i = ∙∙-contract _ _ _ (_ , β) (~ i) .fst

cong₂-∙∙
  : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (f : A → B → C)
  → {a b c d : A} (α : a ≡ b) (β : b ≡ c) (γ : c ≡ d)
  → {w x y z : B} (ξ : w ≡ x) (ψ : x ≡ y) (ω : y ≡ z)
  →   cong₂ f (α ∙∙ β ∙∙ γ) (ξ ∙∙ ψ ∙∙ ω)
    ≡ cong₂ f α ξ ∙∙ cong₂ f β ψ ∙∙ cong₂ f γ ω
cong₂-∙∙ f α β γ ξ ψ ω =
  ∙∙-unique' λ i j → f (∙∙-filler α β γ i j)
                       (∙∙-filler ξ ψ ω i j)

cong₂-∙
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (f : A → B → C)
  → {a b c : A} (α : a ≡ b) (β : b ≡ c)
  → {w x y : B} (ξ : w ≡ x) (ψ : x ≡ y)
  → cong₂ f (α ∙ β) (ξ ∙ ψ) ≡ cong₂ f α ξ ∙ cong₂ f β ψ
cong₂-∙ f α β ξ ψ = cong₂-∙∙ f refl α β refl ξ ψ

-- -}
-- -}
-- -}
-- -}
