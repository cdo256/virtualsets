module VSet.Path where

open import Cubical.Foundations.Prelude renaming (_∎ to _▯)
open import Cubical.Foundations.Path public
open import Cubical.Foundations.Transport public hiding (transpEquiv)
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Prod.Base
open import Cubical.Data.Prod.Properties

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

Singleton : ∀ {ℓ} {A : Type ℓ} → A → Type _
Singleton x = Σ[ y ∈ _ ] x ≡ y

inspect' : ∀ {ℓ} {A : Type ℓ} (x : A) → Singleton x
inspect' x = x , refl

module _ {A : Type ℓ} {B : A -> Type ℓ'} where
  inspect'' : (f : (x : A) → B x) (x : A) → B x × (Reveal f · x is f x)
  inspect'' f x = f x , inspect f x


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
    -- so contract that to a point to give a non-dependent path.
    subst (λ ○ → PathP (λ i → B (○ i))
                 (transport (λ i → B (f (p i))) (g a))
                 (g (transport (λ i → B (p i)) a)))
          (lCancel (cong f p)) composite

subst2-reorder
  : ∀ {ℓ ℓ'} {A A' : Type ℓ} (B : A → A' → Type ℓ') {x y : A} {w z : A'}
  → (f : A → A) (f' : A' → A') (g : {z : A} {z' : A'} → B z z' → B (f z) (f' z'))
  → (p : x ≡ y) (q : w ≡ z) (a : B x w)
  → transport (λ i → B (f (p i)) (f' (q i))) (g a)
  ≡ g (transport (λ i → B (p i) (q i)) a)
subst2-reorder B f f' g p q a = 
  let 
    step1 : (λ j → B (f (p (~ j))) (f' (q (~ j))))
      [ transport (λ i → B (f (p i)) (f' (q i))) (g a)
      ≡ g a
      ]
    step1 = symP (transport-filler (λ i → B (f (p i)) (f' (q i))) (g a))
    step2 : (λ j → B (f (p j)) (f' (q j)))
      [ g a
      ≡ g (transport (λ i → B (p i) (q i)) a)
      ]
    step2 = congP (λ i ○ → g ○) (transport-filler (λ i → B (p i) (q i)) a)
    composite : (λ i → B ((sym (cong f p) ∙ (cong f p)) i)
                         ((sym (cong f' q) ∙ (cong f' q)) i))
      [ transport (λ i → B (f (p i)) (f' (q i))) (g a)
      ≡ g (transport (λ i → B (p i) (q i)) a)
      ]
    composite = compPathP' {B = λ x → {!!}} step1 step2
  in
    -- Our path index goes out and back along the same path,
    -- so contract that to a point to give a non-dependent path.
    subst2 (λ ○ ◻ → PathP (λ i → B (○ i) (◻ i))
                 (transport (λ i → B (f (p i)) (f' (q i))) (g a))
                 (g (transport (λ i → B (p i) (q i)) a)))
          (lCancel (cong f p)) (lCancel (cong f' q)) composite

subst-reorder
  : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {x y : A}
  → (f : A → A) (g : {z : A} → B z → B (f z)) (p : x ≡ y) (a : B x)
  → subst B (cong f p) (g a)
  ≡ g (subst B p a)
subst-reorder B f g p a = transport-reorder B f g p a

subst-reorder'
  : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') (B' : A → Type ℓ') {x y : A}
  → (g : {z : A} → B z → B' z) (p : x ≡ y) (a : B x)
  → subst B' p (g a)
  ≡ g (subst B p a)
subst-reorder' B B' g p a = 
  let 
    step1 : (λ j → B' (p (~ j)))
      [ transport (λ i → (B' (p i))) (g a)
      ≡ g a
      ]
    step1 = symP (transport-filler (λ i → (B' (p i))) (g a))
    step2 : (λ j → (B' (p j)))
      [ g a
      ≡ g (transport (λ i → B (p i)) a)
      ]
    step2 = congP (λ i ○ → g ○) (transport-filler (λ i → B (p i)) a)
    composite : (λ i → B' ((sym p ∙ p) i))
      [ transport (λ i → (B' (p i))) (g a)
      ≡ g (transport (λ i → B (p i)) a)
      ]
    composite = compPathP' {B = B'} step1 step2
  in
    -- Our path index goes out and back along the same path,
    -- so contract that to a point to give a non-dependent path.
    subst (λ ○ → PathP (λ i → B' (○ i))
                 (transport (λ i → (B' (p i))) (g a))
                 (g (transport (λ i → B (p i)) a)))
          (lCancel p) composite


subst2-reorder'
  : ∀ {ℓ ℓ'} {A A' : Type ℓ}
    (B : A → A' → Type ℓ') (B' : A → A' → Type ℓ')
    {x y : A} {w z : A'}
  → (g : {z : A} {z' : A'} → B z z' → B' z z')
  → (p : x ≡ y) (q : w ≡ z) (a : B x w)
  → subst2 B' p q (g a) ≡ g (subst2 B p q a)
subst2-reorder' B B' g p q a =
  let
    step1 : (λ j → B' (p (~ j)) (q (~ j)))
      [ transport (λ i → B' (p i) (q i)) (g a) ≡ g a ]
    step1 = symP (transport-filler (λ i → B' (p i) (q i)) (g a))

    step2 : (λ j → B' (p j) (q j))
      [ g a ≡ g (transport (λ i → B (p i) (q i)) a) ]
    step2 = congP (λ i ○ → g ○) (transport-filler (λ i → B (p i) (q i)) a)

    composite : (λ i → B' ((sym p ∙ p) i) ((sym q ∙ q) i))
      [ transport (λ i → B' (p i) (q i)) (g a) ≡ g (transport (λ i → B (p i) (q i)) a) ]
    composite = compPathP' {B = λ x → B' (proj₁ x) (proj₂ x)}
                           step1 step2
  in subst2 (λ ○ □ → PathP (λ i → B' (○ i) (□ i))
                   (transport (λ i → B' (p i) (q i)) (g a))
                   (g (transport (λ i → B (p i) (q i)) a)) )
        (lCancel p) (lCancel q) composite

      
resubst : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ')
        → (c : (z : A) → B z)
        → {x y : A} (p : x ≡ y)
        → c y ≡ subst B p (c x)
resubst B c {x = x} {y = y} p =
  let step1 : (λ i → B (p (~ i))) [ c y ≡ c x ]
      step1 i = c (p (~ i))
      step2 : (λ i → B (p i))
            [ c x
            ≡ subst B p (c x)
            ]
      step2 = transport-filler (λ i → B (p i)) (c x)
      composite : (λ i → B ((sym p ∙ p) i))
        [ c y
        ≡ subst B p (c x)
        ]
      composite = compPathP' {B = B} step1 step2
  in subst (λ ○ → PathP (λ i → (B (○ i)))
                  (c y)
                  (subst B p (c x)))
           (lCancel p) composite

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

transport-inj
  : ∀ {ℓ} {A B : Type ℓ} {x y : A} (p : A ≡ B)
  → transport p x ≡ transport p y
  → x ≡ y
transport-inj {x = x} {y = y} p q =
  x ≡⟨ sym (transport⁻Transport p x) ⟩
  transport (sym p) (transport p x) ≡⟨ cong (transport (sym p)) q ⟩
  transport (sym p) (transport p y) ≡⟨ transport⁻Transport p y ⟩
  y ▯ 

subst2-stack : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ'} (C : A → B → Type ℓ'')
             → {a1 a2 : A} {b1 b2 : B} (p : a1 ≡ a2) (q : b1 ≡ b2) (x : C a1 b1)
             → subst2 C p refl (subst2 C refl q x) ≡ subst2 C p q x
subst2-stack C p q x = J (λ b' q → subst2 C p refl (subst2 C refl q x) ≡ subst2 C p q x) r q
  where
    r : subst2 C p refl (subst2 C refl refl x)
      ≡ subst2 C p refl x
    r = cong (subst2 C p refl) (transportRefl x)

subst2-stack' : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ'} (C : A → B → Type ℓ'')
             → {a1 a2 : A} {b1 b2 : B} (p : a1 ≡ a2) (q : b1 ≡ b2) (x : C a1 b1)
             → subst2 C refl q (subst2 C p refl x) ≡ subst2 C p q x
subst2-stack' C p q x = J (λ _ q → subst2 C refl q (subst2 C p refl x) ≡ subst2 C p q x) r q
  where
    r : subst2 C refl refl (subst2 C p refl x)
      ≡ subst2 C p refl x
    r = transportRefl (subst2 C p refl x)

module Tests where
  open import Cubical.Data.Nat
  open import Cubical.Data.Unit

  foo : (λ i → ℕ) [ 1 + 1 ≡ 2 + 0 ]
  foo = (1 + 1) ≡P[ tt ][ refl ∙P refl ]⟨ (λ _ → ℕ) ➢ refl ⟩ 
        2 ≡P[ tt ][ refl ∙P refl ]⟨ (λ _ → ℕ) ➢ (+-zero 2) ⟩ 
        2 + 0 ∎P

  foo' : (λ i → ℕ) [ 1 + 1 ≡ 2 + 0 ]
  foo' = compPathP'  {x = tt} {B = λ _ → ℕ} {p = refl} {q = refl} refl
        (compPathP'  {x = tt} {B = λ _ → ℕ} {p = refl} {q = refl} ((+-zero 2)) refl)

