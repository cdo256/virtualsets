module VSet.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path public
open import Cubical.Foundations.Transport public hiding (transpEquiv)
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)


private
  variable
    ℓ : Level

_≢_ : ∀ {ℓ} {A : Type ℓ} → (x y : A) → Type ℓ
x ≢ y = x ≡ y → ⊥

≢sym : {A : Type ℓ} {x y : A} → (x ≢ y) → (y ≢ x)
≢sym x≢y y≡x = x≢y (sym y≡x)

≢cong : ∀ {A B : Type} {x y : A} (f : A → B) → f x ≢ f y → x ≢ y
≢cong {A} {B} {x} {y} f fx≢fy x≡y = fx≢fy (cong f x≡y)

subst-inv : ∀ {A : Type} {x y : A} (B : A → Type) (p : x ≡ y) → (pa : B y)
          → subst B p (subst B (sym p) pa) ≡ pa
subst-inv {A} {x} {y} B p a = 
  subst B p (subst B (sym p) a) ≡⟨ refl ⟩
  subst B p (transport (λ i → B (p (~ i))) a)
    ≡⟨ transportTransport⁻ (λ i → B (p i)) a ⟩
  a ∎

-- cong-∙∙ : ∀ {B : Type ℓ} (f : A → B) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
--           → cong f (p ∙∙ q ∙∙ r) ≡ (cong f p) ∙∙ (cong f q) ∙∙ (cong f r)
-- cong-∙∙ f p q r j i = cong-∙∙-filler f p q r i1 j i

-- cong-∙ : ∀ {B : Type ℓ} (f : A → B) (p : x ≡ y) (q : y ≡ z)
--          → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
-- cong-∙ f p q = cong-∙∙ f refl p q

1LabSquare
  : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  → (p : a00 ≡ a01) (q : a00 ≡ a10) (s : a01 ≡ a11) (r : a10 ≡ a11)
  → Type ℓ
1LabSquare p q s r = Square p r q s

∂ : I → I
∂ i  = i ∨ ~ i

--- 1Lab
-- hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
--       → ((i : I) → Partial (φ ∨ ~ i) A)
--       → A
-- hfill φ i u = hcomp (φ ∨ ~ i) λ where
--   j (φ = i1) → u (i ∧ j) 1=1
--   j (i = i0) → u i0 1=1
--   j (j = i0) → u i0 1=1

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


--- 1Lab
-- ∙∙-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
--           → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
--           → Square (sym p) q (p ∙∙ q ∙∙ r) r
-- ∙∙-filler p q r i j = hfill (∂ j) i λ where
--   k (j = i0) → p (~ k)
--   k (j = i1) → r k
--   k (k = i0) → q j

module 1Lab where
  hcomp
    : ∀ {ℓ} {A : Type ℓ} (φ : I)
    → (u : (i : I) → Partial (φ ∨ ~ i) A)
    → A
  hcomp {A = A} φ u = X.primHComp sys (u i0 1=1) module hcomp-sys where
    sys : ∀ j → Partial φ A
    sys j (φ = i1) = u j 1=1

  hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
        → ((i : I) → Partial (φ ∨ ~ i) A)
        → A
  hfill φ i u = hcomp (φ ∨ ~ i) λ where
    j (φ = i1) → u (i ∧ j) 1=1
    j (i = i0) → u i0 1=1
    j (j = i0) → u i0 1=1

  doubleHComp : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
              → w ≡ x → x ≡ y → y ≡ z
              → w ≡ z
  doubleHComp p q r i = hcomp (λ j _ → {!!}) {!!} {!!}

∙∙-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → Square (sym p) r q (p ∙∙ q ∙∙ r)
∙∙-filler {A} {w} {x} {y} {z} p q r i j =
  hfill {φ = {!~ j ∨ j ∨ (~ i ∧ ~ j)!}}
        {!λ { k (j = i0) → p (~ i)
           ; k (i = i0) → ?
           ; k (j = i1) → r i}!}
        {!q ?!}
        {!i!}

-- ∙∙-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
--           → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
--           → Square (sym p) r q (p ∙∙ q ∙∙ r)
-- ∙∙-filler p q r i j = hfill {A = {!!}} {φ = ∂ j} {!!} {!!} {!!}
{-
module DoubleCompUnique {ℓ : Level} {A : Type ℓ}
    {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    (α' β' : Σ[ s ∈ w ≡ z ] Square (sym p) r q s) where

  α = fst α'
  α-fill = snd α'

  β = fst β'
  β-fill = snd β'

  -- cube' : (i j k l : I) → .(isOne : IsOne (∂ i ∨ ∂ k)) → {!p (~ j) ≡ r j!}
  -- cube' i j k l γ (i = i0) = {!α-fill l k!}
  -- cube' i j k l γ (i = i1) = {!β-fill l k!}
  -- cube' i j k l γ (k = i0) = {!p (~ l)!}
  -- cube' i j k l γ (k = i1) = {!r l!}
  -- cube' i j k l γ (l = i0) = {!q k!}

  cube'' : (i j k l : I) → .(isOne : IsOne (∂ i ∨ ∂ k)) → {!p (~ j) ≡ r j!}
  cube'' i j k = λ where
    l γ (i = i0) → {!α-fill l k!}
    l γ (i = i1) → {!β-fill l k!}
    l γ (k = i0) → {!p (~ l)!}
    l γ (k = i1) → {!r l!}
    l γ (l = i0) → {!q k!}


  cube : (i j : I) → p (~ j) ≡ r j
  -- cube i j k = hfill {A = A} {φ = ∂ i ∨ ∂ k} {!!} {!!} {!!}
  
  ∙∙-unique : α' ≡ β'
  ∙∙-unique = {!!}

open DoubleCompUnique using (∙∙-unique)

∙∙-contract : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → (β : Σ[ s ∈ (w ≡ z) ] Square (sym p) r q s)
            → (p ∙∙ q ∙∙ r , ∙∙-filler p q r) ≡ β
∙∙-contract p q r β = ∙∙-unique p q r _ β

module DoubleCompUnique' {ℓ : Level} {A : Type ℓ}
    {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    {s : w ≡ z} (β : Square (sym p) r q s) where

  ∙∙-unique' : s ≡ p ∙∙ q ∙∙ r
  ∙∙-unique' i = ∙∙-contract _ _ _ (_ , β) (~ i) .fst



{-
module _ {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (f : A → B → C)
  {a b c d : A} (α : a ≡ b) (β : b ≡ c) (γ : c ≡ d)
  {w x y z : B} (ξ : w ≡ x) (ψ : x ≡ y) (ω : y ≡ z) where

  ∙∙-unique' : ((i j : I) → {!!}) → {!!}
  ∙∙-filler : {!!}

  cong₂-∙∙ : cong₂ f (α ∙∙ β ∙∙ γ) (ξ ∙∙ ψ ∙∙ ω)
           ≡ cong₂ f α ξ ∙∙ cong₂ f β ψ ∙∙ cong₂ f γ ω
  cong₂-∙∙ =
    ∙∙-unique' (λ i j → f (∙∙-filler α β γ i j)
                          (∙∙-filler ξ ψ ω i j))

  cong₂-∙
    : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
    → (f : A → B → C)
    → {a b c : A} (α : a ≡ b) (β : b ≡ c)
    → {w x y : B} (ξ : w ≡ x) (ψ : x ≡ y)
    → cong₂ f (α ∙ β) (ξ ∙ ψ) ≡ cong₂ f α ξ ∙ cong₂ f β ψ
  cong₂-∙ f α β ξ ψ = cong₂-∙∙ f refl α β refl ξ ψ

-- -}

-- -}
