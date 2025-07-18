module Compat.1Lab.Dependent where

open import Cubical.Foundations.Prelude as Cubical
  renaming ( hcomp to cubical-hcomp
           ; comp to cubical-comp
           ; hfill to cubical-hfill
           )
open import Compat.1Lab.Path

-- primHComp  : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A

1lab-comp
  : ∀ {ℓ : I → Level} (A : (i : I) → Type (ℓ i)) (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
  → A i1
1lab-comp A φ u = cubical-hcomp sys (transp (λ i → A i) i0 (u i0 1=1)) where
  sys : ∀ j → Partial φ (A i1)
  sys i (φ = i1) = transp (λ j → A (i ∨ j)) i (u i 1=1)

{-
 w       q          z
a10 -------------> a11
 A                  |
 |                  |
 |                  |
 | p                | r
 |                  |     A j
 |                  V     |
 x        s         y     |
a00 -------------> a01    +-----> i
-}

{-
1lab-∙∙-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → Square q (p ∙∙ q ∙∙ r) (sym p) r
-- 1lab-∙∙-filler p q r i j = compat-hfill (∂ j) i λ where
--   k (j = i0) → p (~ k)
--   k (j = i1) → r k
--   k (k = i0) → q j

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

-- {-

module DoubleCompUnique {ℓ : Level} {A : Type ℓ}
    {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    (α' β' : Σ[ s ∈ w ≡ z ] Square q s (sym p) r) where

  α = fst α'
  α-fill = snd α'

  β = fst β'
  β-fill = snd β'

  φ : (i j k : I) → I
  φ i j k = (∂ i ∨ ∂ k)

  g : (i k j : I) → Partial (~ i ∨ i ∨ ~ k ∨ k ∨ ~ j) A
  g i k j (i = i0) = α-fill j k
  g i k j (i = i1) = β-fill j k
  g i k j (k = i0) = p (~ j)
  g i k j (k = i1) = r j
  g i k j (j = i0) = q k

  hfill : ∀ {ℓ} (φ j : I)
        → ((i : I) → Partial (φ ∨ ~ i) A)
        → A
  hfill φ j u = hcomp where
    f : (l : I) → Partial (φ ∨ ~ j ∨ ~ l) A
    f l (φ = i1) = u (j ∧ l) 1=1
    f l (j = i0) = u i0 1=1
    f l (l = i0) = u i0 1=1

    sys : ∀ l → Partial (φ ∨ ~ j) A
    sys l (φ = i1) = f l 1=1
    sys l (j = i0) = f l 1=1

    hcomp : A
    hcomp  = cubical-hcomp sys (u i0 1=1)

  cube : (i j : I) → p (~ j) ≡ r j
  cube i j k = hfill (∂ i ∨ ∂ k) j (g i k)

  square : α ≡ β
  square i j = cube i i1 j
  
  ∙∙-unique : α' ≡ β'
  ∙∙-unique = λ i → (λ j → square i j) , (λ j k → cube i j k)

open DoubleCompUnique using (∙∙-unique)


∙∙-contract : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → (β : Σ[ s ∈ (w ≡ z) ] Square q s (sym p) r)
            → (p ∙∙ q ∙∙ r , compat-∙∙-filler p q r) ≡ β
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
  ∙∙-unique' λ i j → f (compat-∙∙-filler α β γ i j)
                       (compat-∙∙-filler ξ ψ ω i j)

cong₂-∙
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  → (f : A → B → C)
  → {a b c : A} (α : a ≡ b) (β : b ≡ c)
  → {w x y : B} (ξ : w ≡ x) (ψ : x ≡ y)
  → cong₂ f (α ∙ β) (ξ ∙ ψ) ≡ cong₂ f α ξ ∙ cong₂ f β ψ
cong₂-∙ f α β ξ ψ = cong₂-∙∙ f refl α β refl ξ ψ

-- cong₂ : {C : (a : A) → (b : B a) → Type ℓ} →
--         (f : (a : A) → (b : B a) → C a b) →
--         (p : x ≡ y) →
--         {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
--         PathP (λ i → C (p i) (q i)) (f x u) (f y v)
-- cong₂ f p q i = f (p i) (q i)
-- {-# INLINE cong₂ #-}

-- \Mi - math italic
cong₂-∙-dep
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (𝑎 : A) → B 𝑎 → Type ℓ''}
  → (f : (𝑎 : A) → (𝑏 : B 𝑎) → C 𝑎 𝑏)
  → {a b c : A} (α : a ≡ b) (β : b ≡ c)
  → {w : B a} {x : B b} {y : B c}
  → (ξ : PathP (λ i  → B (α i)) w x)
  → (ψ : PathP (λ i  → B (β i)) x y)
  → cong₂ f (α ∙ β) {!ξ ∙₂ ψ!} ≡ {!!}
  → cong₂ f (α ∙ β) {!ξ ∙ ψ!} ≡ ({!cong₂ f α ξ!} ∙ {!cong₂ f β ψ!}) {!!}
cong₂-∙-dep f α β ξ ψ = {!cong₂-∙∙-dep f refl α β refl ξ ψ!}


-- -}
-- -}


-- _∙P'_
--   : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
--   → {a b c : A} {α : a ≡ b} {β : b ≡ c}
--   → {w : B a} {x : B b} {y : B c}
--   → (ξ : PathP (λ i → B (α i)) w x)
--   → (ψ : PathP (λ i → B (β i)) x y)
--   → PathP (λ i → B ((α ∙ β) i)) w y
-- _∙P'_ {B = B} ξ ψ = compPathP' {B = B} ξ ψ

-- _∙P_
--   : ∀ {ℓ ℓ'} {A A' : Type ℓ} {B : A → Type ℓ'} {C : A' → Type ℓ'}
--   → {a b c : A} {α : a ≡ b} {β : b ≡ c}
--   → {w : B a} {x : B b} {y : B c}
--   → (ξ : PathP (λ i → B (α i)) w x)
--   → (ψ : PathP (λ i → B (β i)) x y)
--   → PathP (λ i → B ((α ∙ β) i)) w y
-- _∙P_ {B = B} ξ ψ = compPathP' {B = B} ξ ψ
