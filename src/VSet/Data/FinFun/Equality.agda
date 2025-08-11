module VSet.Data.FinFun.Equality where

open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.FinFun.Injection

open import Cubical.Foundations.Equiv.Base 

infix 8 _≈_

record _≈_ {A B X Y : ℕ} (f : [ A ↣ X ]) (g : [ B ↣ Y ]) : Type where
  field
    p : A ≡ B
    q : X ≡ Y
    path : (λ i → cong₂ FinFun p q i) [ fst f ≡ fst g ]

≈refl : {A X : ℕ} (f : [ A ↣ X ]) → f ≈ f
≈refl {A} {X} f = record
  { p = refl
  ; q = refl
  ; path = λ i x → fst f x
  }

≈sym : ∀ {A B X Y : ℕ} {f : [ A ↣ X ]} {g : [ B ↣ Y ]} → f ≈ g → g ≈ f
≈sym {A} {B} {X} {Y} {f} {g} f≈g = record
  { p = sym p 
  ; q = sym q
  ; path = λ i → path (~ i)
  }
  where
    open _≈_ f≈g


module Trans {A B C X Y Z : ℕ}
           {f : [ A ↣ X ]}
           {g : [ B ↣ Y ]}
           {h : [ C ↣ Z ]}
           (g≈h : g ≈ h) (f≈g : f ≈ g) where

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
      path : (λ j → (cong₂ FinFun p1 q1 ∙ cong₂ FinFun p2 q2) j) [ fst f ≡ fst h ]
      path = compPathP path1 path2
      path' : (λ j → (cong₂ FinFun (p1 ∙ p2) (q1 ∙ q2)) j) [ fst f ≡ fst h ]
      path' = subst⁻ (λ ○ → (λ j → ○ j) [ fst f ≡ fst h ]) c2 path

  infixl 4 _∘≈_ 
  _∘≈_ : f ≈ h
  _∘≈_ = ≈trans

open Trans using (≈trans; _∘≈_) public

-- reverse composition
infixl 4 _≈∘_
_≈∘_ : {A B C X Y Z : ℕ}
       {f : [ A ↣ X ]}
       {g : [ B ↣ Y ]}
       {h : [ C ↣ Z ]}
       (f≈g : f ≈ g) (g≈h : g ≈ h) → f ≈ h
f≈g ≈∘ g≈h = ≈trans g≈h f≈g


-- ≈⁻∘≈ : ∀ {A B X Y : ℕ} {f : [ A ↣ X ]} {g : [ B ↣ Y ]}
--      → (f≈g : f ≈ g) → f≈g ∘≈ ≈sym f≈g ≡ ≈refl f
-- ≈⁻∘≈ {A = A} {B = B} {X = X} {f = f} f≈g i ._≈_.p = refl i
-- ≈⁻∘≈ {A = A} {B = B} {X = X} {f = f} f≈g i ._≈_.q = refl i
-- ≈⁻∘≈ {A = A} {B = B} {X = X} {f = f} f≈g i ._≈_.path = refl 


-- step-≈ : {A B C X Y Z : ℕ}
--        → (f : [ A ↣ X ]) → {g : [ B ↣ Y ]} → {h : [ C ↣ Z ]}
--        → f ≈ g → g ≈ h → f ≈ h
-- step-≈ _ f≈g g≈h =  g≈h ∘≈ f≈g

-- syntax step-≈ f g f≈g = f ≈⟨ f≈g ⟩ g

-- infixr 2 ≈⟨⟩-syntax
-- syntax ≈⟨⟩-syntax f g (λ i → B) = f ≈[ i ]⟨ B ⟩ g

infixr 2 _≈⟨_⟩_
_≈⟨_⟩_ : {A B C X Y Z : ℕ}
       → (f : [ A ↣ X ]) → {g : [ B ↣ Y ]} → {h : [ C ↣ Z ]}
       → f ≈ g → g ≈ h → f ≈ h
_ ≈⟨ f≈g ⟩ g≈h = g≈h ∘≈ f≈g

infix 3 _∎
_∎ : {A X : ℕ} → (f : [ A ↣ X ]) → f ≈ f
f ∎ = ≈refl f


≈transport : ∀ {A B X Y : ℕ} → A ≡ B → X ≡ Y → [ A ↣ X ] → [ B ↣ Y ]
≈transport {A = A} {B = B} p q f = X↣Y ↣∘↣ f ↣∘↣ B↣A
  where
    B↣A = ≡to↣ (cong Fin (sym p))
    X↣Y = ≡to↣ (cong Fin q)

≈transport-fun : ∀ {A B X Y : ℕ} → A ≡ B → X ≡ Y
               → (⟦ A ⟧ → ⟦ X ⟧) → ⟦ B ⟧ → ⟦ Y ⟧
≈transport-fun p q f =
  subst Fin q ∘ f ∘ subst Fin (sym p)

≈transport-filler : ∀ {A B X Y : ℕ} → (p : A ≡ B) → (q : X ≡ Y)
                  → (f : [ A ↣ X ]) → f ≈ ≈transport p q f
≈transport-filler {A = A} {B} {X} {Y} p q f =
  record { p = p ; q = q ; path = path }
  where
    B↣A = ≡to↣ (cong Fin (sym p))
    X↣Y = ≡to↣ (cong Fin q)
    P = cong₂ FinFun p q
    path : (λ i → cong₂ FinFun p q i)
      [ fst f
      ≡ subst Fin q ∘ fst f ∘ subst Fin (sym p)
      ]
    path = subst2-filler FinFun p q (fst f)

from≡ : ∀ {A X : ℕ} → {f g : [ A ↣ X ]}
      → fst f ≡ fst g → f ≈ g
from≡ path = record
  { p = refl
  ; q = refl
  ; path = path
  }

is-transport : ∀ {X Y : ℕ} → (f : [ X ↣ Y ]) → Type
is-transport {X} {Y} f = Σ[ p ∈ X ≡ Y ] fst f ≡ subst Fin p
