module VSet.Data.SomeFin.Equality where

open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection

open import Cubical.Foundations.Equiv.Base 

infix 8 _≈_

record _≈_ {A B X Y : ℕ} (f : Fin A → Fin X) (g : Fin B → Fin Y) : Type where
  field
    p : A ≡ B
    q : X ≡ Y
    path : (λ i → cong₂ FinFun p q i) [ f ≡ g ]

≈refl : {A X : ℕ} (f : Fin A → Fin X) → f ≈ f
≈refl {A} {X} f = record
  { p = refl
  ; q = refl
  ; path = λ i x → f x
  }

≈sym : ∀ {A B X Y : ℕ} {f : Fin A → Fin X} {g : Fin B → Fin Y} → f ≈ g → g ≈ f
≈sym {A} {B} {X} {Y} {f} {g} f≈g = record
  { p = sym p 
  ; q = sym q
  ; path = λ i → path (~ i)
  }
  where
    open _≈_ f≈g

-- ≈transp : ∀ {A B X Y : ℕ} {f : Fin A → Fin X} {g : Fin B → Fin Y}
--         → (f≈g : f ≈ g) → (i : I) → (h : () )

module Trans {A B C X Y Z : ℕ}
           {f : Fin A → Fin X}
           {g : Fin B → Fin Y}
           {h : Fin C → Fin Z}
           (f≈g : f ≈ g) (g≈h : g ≈ h) where

  open _≈_ f≈g renaming (p to p1; q to q1; path to path1)
  open _≈_ g≈h renaming (p to p2; q to q2; path to path2)
  r1 : FinFun A X ≡ FinFun B Y
  r1 i = FinFun (p1 i) (q1 i)
  r2 : FinFun B Y ≡ FinFun C Z
  r2 i = FinFun (p2 i) (q2 i)

  open import Compat.1Lab.Path using (cong₂-∙)

  ≈trans : f ≈ h
  ≈trans = record
    { p = p1 ∙ p2
    ; q = q1 ∙ q2
    ; path = path'
    }
    where
      c2 : cong₂ FinFun (p1 ∙ p2) (q1 ∙ q2) ≡
           cong₂ FinFun p1 q1 ∙ cong₂ FinFun p2 q2
      c2 = cong₂-∙ FinFun p1 p2 q1 q2
      path : (λ j → (cong₂ FinFun p1 q1 ∙ cong₂ FinFun p2 q2) j) [ f ≡ h ]
      path = compPathP path1 path2
      path' : (λ j → (cong₂ FinFun (p1 ∙ p2) (q1 ∙ q2)) j) [ f ≡ h ]
      path' = subst⁻ (λ ○ → PathP (λ j → ○ j) f h) c2 path
  _∘≈_ : f ≈ h
  _∘≈_ = ≈trans

open Trans using (≈trans; _∘≈_)

≈⁻∘≈ : ∀ {A B X Y : ℕ} {f : Fin A → Fin X} {g : Fin B → Fin Y}
     → (f≈g : f ≈ g) → f≈g ∘≈ ≈sym f≈g ≡ ≈refl f
≈⁻∘≈ {A = A} {B = B} {X = X} {f = f} f≈g i ._≈_.p = refl i
≈⁻∘≈ {A = A} {B = B} {X = X} {f = f} f≈g i ._≈_.q = refl i
≈⁻∘≈ {A = A} {B = B} {X = X} {f = f} f≈g i ._≈_.path = refl 
