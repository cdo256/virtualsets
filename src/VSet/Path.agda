module VSet.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path public
open import Cubical.Foundations.Transport public hiding (transpEquiv)
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)


private
  variable
    ℓ ℓ' ℓ'' : Level



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

-- step-≡P : {A : I → Type ℓ} {x : A i0} {y : A i1} {B_i1 : Type ℓ} {B : (A i1) ≡ B_i1} {z : B i1}
--         → PathP A x y → PathP (λ i → B i) y z → PathP (λ j → ((λ i → A i) ∙ B) j) x z
-- step-≡P = compPathP     


-- module DependentPathSyntax where
private
  variable
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A
    p : x ≡ y
    q : y ≡ z

step-≡P : ∀ (B : A → Type ℓ')
          → (x' : B x) {y' : B y} {z' : B z} 
          → (P : PathP (λ i → B (p i)) x' y')
          → (Q : PathP (λ i → B (q i)) y' z')
          → PathP (λ i → B ((p ∙ q) i)) x' z'
step-≡P B x' P Q = compPathP' {B = B} {x' = x'} P Q

syntax step-≡P B x' P Q = x' ≡P[ B ]⟨ P ⟩ Q

infixr 2 ≡P⟨⟩-syntax
≡P⟨⟩-syntax : (x : A) → y ≡ z → x ≡ y → x ≡ z
≡P⟨⟩-syntax = step-≡

infix 3 _∎P
_∎P : {A : Type ℓ} (x : A) → x ≡ x
_ ∎P = refl


-- open DependentPathSyntax public
