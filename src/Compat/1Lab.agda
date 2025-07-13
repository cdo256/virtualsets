module Compat.1Lab where

open import Cubical.Foundations.Prelude as Cubical
  renaming ( hcomp to cubical-hcomp
           ; hfill to cubical-hfill
           ; Square to cubical-Square
           )

∂ : I → I
∂ i  = i ∨ ~ i

Square
  : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  → (p : a00 ≡ a01) (q : a00 ≡ a10) (s : a01 ≡ a11) (r : a10 ≡ a11)
  → Type ℓ
Square p q s r = PathP (λ i → p i ≡ r i) q s  -- cubical-Square p s r q?

hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
hcomp {A = A} φ u = cubical-hcomp sys (u i0 1=1) module hcomp-sys where
  sys : ∀ j → Partial φ A
  sys j (φ = i1) = u j 1=1

hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u = hcomp (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1

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

∙∙-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → Square (sym p) q (p ∙∙ q ∙∙ r) r
∙∙-filler p q r i j = hfill (∂ j) i λ where
  k (j = i0) → p (~ k)
  k (j = i1) → r k
  k (k = i0) → q j

module DoubleCompUnique {ℓ : Level} {A : Type ℓ}
    {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    (α' β' : Σ[ s ∈ w ≡ z ] Square (sym p) q s r) where

  α = fst α'
  α-fill = snd α'

  β = fst β'
  β-fill = snd β'

  cube : (i j : I) → p (~ j) ≡ r j
  cube i j k = hfill (∂ i ∨ ∂ k) j λ where
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

∙∙-contract : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → (β : Σ[ s ∈ (w ≡ z) ] Square (sym p) q s r)
            → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ≡ β
∙∙-contract p q r β = ∙∙-unique p q r _ β

∙∙-unique'
  : {ℓ : Level} {A : Type ℓ}
  → {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
  → (β : Square (sym p) q s r)
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
