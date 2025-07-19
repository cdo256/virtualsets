module VSet.Path where

open import Cubical.Foundations.Prelude renaming (_∎ to _▯)
open import Cubical.Foundations.Path public
open import Cubical.Foundations.Transport public hiding (transpEquiv)
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Foundations.GroupoidLaws


private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

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
  a ▯

transport-reorder
  : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {x y : A}
  → (f : A → A) (g : {z : A} → B z → B (f z)) (p : x ≡ y) (a : B x)
  → transport (λ i → B (f (p i))) (g a)
  ≡ g (transport (λ i → B (p i)) a)
transport-reorder B f g p a =
  let 
    step1 : (λ j → B (f (p (~ j))))
      [ transport (λ i → B (f (p i))) (g a)
      ≡ g a
      ]
    step1 = symP (transport-filler (λ i → B (f (p i))) (g a))
    step2 : (λ j → B (f (p j)))
      [ g a
      ≡ g (transport (λ i → B (p i)) a)
      ]
    step2 = congP (λ i ○ → g ○) (transport-filler (λ i → B (p i)) a)
    composite : (λ i → B ((sym (cong f p) ∙ (cong f p)) i))
      [ transport (λ i → B (f (p i))) (g a)
      ≡ g (transport (λ i → B (p i)) a)
      ]
    composite = compPathP' {B = B} step1 step2
  in
    -- Our path index goes out and back along the same path,
    -- so contract that to a point, so we have a non-dependent path.
    subst (λ ○ → PathP (λ i → B (○ i))
                 (transport (λ i → B (f (p i))) (g a))
                 (g (transport (λ i → B (p i)) a)))
          (lCancel (cong f p)) composite


infixr 2 ≡P⟨⟩-syntax
infixr 2 step-≡P 
step-≡P : ∀ (B : A → Type ℓ')
          → (x : A) {y z : A}
          → (p : x ≡ y)
          → (q : y ≡ z)
          → (x' : B x) {y' : B y} {z' : B z}
          → (P : PathP (λ i → B (p i)) x' y')
          → (Q : PathP (λ i → B (q i)) y' z')
          → PathP (λ i → B ((p ∙ q) i)) x' z'
step-≡P B x p q x' P Q = compPathP' {x = x} {B = B} {x' = x'} {p = p} {q = q}  P Q

syntax step-≡P B x p q x' P Q = x' ≡P[ x ][ p ∙P q ]⟨ B ➢ P ⟩ Q

infixr 2 ≡P⟨⟩-syntax
≡P⟨⟩-syntax : ∀ (B : A → Type ℓ')
            → (x : A) {y z : A}
            → (p : x ≡ y)
            → (q : y ≡ z)
            → (x' : B x) {y' : B y} {z' : B z}
            → (P : PathP (λ i → B (p i)) x' y')
            → (Q : PathP (λ i → B (q i)) y' z')
            → PathP (λ i → B ((p ∙ q) i)) x' z'
≡P⟨⟩-syntax B x p q x' P Q = step-≡P B x p q x' P Q 

infix 3 _∎P
_∎P : {A : Type ℓ} (x : A) → x ≡ x
_ ∎P = refl

-- ? ≡P[ ? ][ ? ∙P ? ]⟨ ? ➢ ? ⟩



module Tests where
  open import Cubical.Data.Nat
  open import Cubical.Data.Unit

  foo : (λ i → ℕ) [ 1 + 1 ≡ 2 + 0 ]
  foo = (1 + 1) ≡P[ tt ][ refl ∙P refl ]⟨ (λ _ → ℕ) ➢ refl ⟩ (
        2 ≡P[ tt ][ refl ∙P refl ]⟨ (λ _ → ℕ) ➢ (+-zero 2) ⟩ 
        (2 + 0 ∎P))

  foo' : (λ i → ℕ) [ 1 + 1 ≡ 2 + 0 ]
  foo' = compPathP'  {x = tt} {B = λ _ → ℕ} {p = refl} {q = refl} refl
        (compPathP'  {x = tt} {B = λ _ → ℕ} {p = refl} {q = refl} ((+-zero 2)) refl)

