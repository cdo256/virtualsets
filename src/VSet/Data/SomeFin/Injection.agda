module VSet.Data.SomeFin.Injection where

open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base

[_↣_] : SomeFin → SomeFin → Type
[ X ↣ Y ] = ⟦ X ⟧ ↣ ⟦ Y ⟧

id↣ : ∀ {A} → A ↣ A
id↣ {A} = id , λ x y z → z

infix 8 _≈_ _≈'_

-- _≈_ : {X Y : SomeFin} → (f g : [ X ↣ Y ]) → Type
-- (f , _) ≈ (g , _) = ∀ x → f x ≡ g x

open import Cubical.Foundations.Equiv.Base 

-- record _≈'_ {W X Y Z : SomeFin} (f : [ W ↣ X ]) (g : [ Y ↣ Z ]) : Type where
--   field
--     eq₁ : W ≃ Y
--     eq₂ : X ≃ Z

-- _≈'_ : {W X Y Z : SomeFin} → (f : [ W ↣ X ]) → (g : [ Y ↣ Z ]) → Type
-- (f , _) ≈' (g , _) = {!Σ (p : W ≡ Y) {!Σ (q : X ≡ Z) ∀ x → f x ≡ g x!}!}


⟦x+0⟧≃⟦x⟧ : ∀ (X : SomeFin) → ⟦ X + 0 ⟧ ≃ ⟦ X ⟧ 
⟦x+0⟧≃⟦x⟧ X = transpEquiv (λ i → Fin ((+-zero X) i)) i0


-- fzero≃fzero : (m : ℕ) → (fzero {n = m + 0}) ≡ (fzero {n = m})
-- fzero≃fzero = ?


swap : ⟦ 2 ⟧ → ⟦ 2 ⟧
swap fzero = fsuc fzero
swap (fsuc fzero) = fzero

swap' : ⟦ 2 + 0 ⟧ → ⟦ 2 + 0 ⟧
swap' fzero = fsuc fzero
swap' (fsuc fzero) = fzero

pred' : {n : ℕ} → Fin (suc (suc n) + 0) → Fin (suc n + 0)
pred' fzero = fzero
pred' (fsuc n) = n

-- _≈_ : ∀ {A B X Y : ℕ} → (f : Fin A → Fin X) → (g : Fin B → Fin Y) → Type
-- _≈_ {A} {B} {X} {Y} f g = Σ[ A≡B ∈ A ≡ B ] Σ[ X≡Y ∈ X ≡ Y ]
--   ((a : Fin A) → f a ≡ subst Fin (sym X≡Y) (g (subst Fin A≡B a)))

-- transp-fun : ∀ {A B X Y : ℕ} (A ≡ B) (X ≡ Y) → (Fin A → Fin X) ≡ (Fin B → Fin Y) 
-- transp-fun {A} {B} {X} {Y} p q g = 
--   subst Fin (sym p) (g (subst Fin q a))

_≈'_ : ∀ {A B X Y : ℕ} → (f : Fin A → Fin X) → (g : Fin B → Fin Y) → Type
_≈'_ {A} {B} {X} {Y} f g = Σ[ p ∈ A ≡ B ] Σ[ q ∈ X ≡ Y ]
  ((a : Fin A) → f a ≡ subst Fin (sym q) (g (subst Fin p a)))

_≈''_ : ∀ {A B X Y : ℕ} → (f : Fin A → Fin X) → (g : Fin B → Fin Y) → Type
_≈''_ {A} {B} {X} {Y} f g = Σ[ p ∈ A ≡ B ] Σ[ q ∈ X ≡ Y ]
  let r : PathP (λ i → Type) (Fin A → Fin X) (Fin B → Fin Y)
      r i = (Fin (p i) → Fin (q i))
  in PathP (λ i → r i) f g 

MapPath : ∀ {A B X Y : ℕ} (p : A ≡ B) (p : X ≡ Y)
     → PathP (λ i → Type) (Fin A → Fin X) (Fin B → Fin Y)
MapPath p q i = (Fin (p i) → Fin (q i))

FinFun : ∀ (A B : ℕ) → Type
FinFun A B = Fin A → Fin B

record _≈_ {A B X Y : ℕ} (f : Fin A → Fin X) (g : Fin B → Fin Y) : Type where
  field
    p : A ≡ B
    q : X ≡ Y
    -- path : PathP (λ i → MapPath p q i) f g 
    path : subst2 FinFun p q f ≡ g

-- subst2-filler : {B : Type ℓ'} {z w : B} (C : A → B → Type ℓ'')
--                 (p : x ≡ y) (q : z ≡ w) (c : C x z)
--               → PathP (λ i → C (p i) (q i)) c (subst2 C p q c)
-- subst2-filler C p q = transport-filler (cong₂ C p q)
-- B = ℕ; z = X; w = Y; C = FinFun; p = p; q = q; c = f
-- PathP (λ i → Fin (p i) → Fin (q i)) f (subst2 (Fin p → Fin q) f)


-- subst2 : ∀ {ℓ' ℓ''} { : Type ℓ'} {z w : B} (FinFun : A → B → Type ℓ'')
--         (p : x ≡ y) (q : z ≡ w) → FinFun x z → FinFun y w
-- subst2 FinFun p q f = transport (λ _ → FinFun A X) f

-- module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
--   toPathP : transport (λ i → A i) x ≡ y → PathP A x y
--   toPathP p i = hcomp (λ j → λ { (i = i0) → x
--                                ; (i = i1) → p j })
--                       (transp (λ j → A (i ∧ j)) (~ i) x)

constPath≡refl : {B : Type} → toPathP (λ _ → B) ≡ refl {x = B}
constPath≡refl {B} =
  toPathP {A = λ _ → Type} {x = B} {y = B} (λ _ → B) ≡⟨ refl ⟩
  (λ i → hcomp (λ j → λ { (i = i0) → B
                        ; (i = i1) → (λ _ → B) j })
              (transp (λ j → (λ _ → Type) (i ∧ j)) (~ i) B)) ≡⟨ refl ⟩
  (λ i → hcomp (λ _ _ → B)
              (transp (λ _ → Type) (~ i) B)) ≡⟨ refl ⟩
  refl ∎

-- constPath≡refl' : ∀ {ℓ} {A : Type ℓ} {x : A} → toPathP (λ _ → x) ≡ refl
-- constPath≡refl' {x} =
--   toPathP {A = λ _ → Type} {x = x} {y = x} (λ _ → x) ≡⟨ refl ⟩
--   (λ i → hcomp (λ j → λ { (i = i0) → x
--                         ; (i = i1) → (λ _ → x) j })
--               (transp (λ j → (λ _ → Type) (i ∧ j)) (~ i) x)) ≡⟨ refl ⟩
--   (λ i → hcomp (λ _ _ → x)
--               (transp (λ _ → Type) (~ i) x)) ≡⟨ refl ⟩
--   refl ∎


-- transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
--                    → PathP (λ i → p i) x (transport p x)
-- transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

transpRefl : {A : Type} → (x : A) → transport (λ _ → A) x ≡ x
-- transpRefl x = transport-filler refl {!!} {!!}
transpRefl {A} x =
  transport (λ _ → A) x ≡⟨ cong (λ ○ → transport ○ x) {!constPath≡refl {B = }!} {!!} ⟩
  x ∎
  -- where
  --   const≡refl : toPathP (λ _ → A) ≡ refl {x = A}
  --   const≡refl = constPath≡refl 
  --   TF : PathP (λ i → {!!}) {!!} {!!}
  --   TF = transport-filler {!!} {!!} {!!}

≈refl : {A X : ℕ} (f : Fin A → Fin X) → f ≈ f
≈refl {A} {X} f = record
  { p = refl
  ; q = refl
  ; path = funExt extPath -- λ w → {!subst2-filler (λ x y → FinFun x {!y!})refl refl f !}
  }
  where
    extPath : (w : Fin A) → subst2 FinFun (λ _ → A) (λ _ → X) f w ≡ f w
    extPath w =
      subst2 FinFun (λ _ → A) (λ _ → X) f w ≡⟨ refl ⟩
      transport (λ _ → Fin A → Fin X) f w ≡⟨ transportRefl {!!} {!!} ⟩
      f w ≡⟨ {!!} ⟩
      f w ∎

module Transport (f : {A' X' : ℕ} → Fin A' → Fin X')
                 (g : {B' Y' : ℕ} → Fin B' → Fin Y')
                 -- (path : {A' B' X' Y' : ℕ} {p' : A' ≡ B'} {q' : X' ≡ Y'}
                 --       → PathP (λ i → MapPath p' q' i) f g)
                 where

  module _ {A B X Y : ℕ} (p : A ≡ B) (q : X ≡ Y) where

    f-transform : PathP (λ i → FinFun (p i) (q i)) f (subst2 FinFun p q f)
    f-transform = subst2-filler FinFun p q f

    f' : FinFun B Y
    f' = f-transform i1

    ext : (x : Fin B) → f' x ≡ g x
    ext fzero = {!!}
    ext (fsuc x) = {!!}

    eql : f' ≡ g
    eql = funExt ext

  pointwise : {A B X Y : ℕ} (p : A ≡ B) (q : X ≡ Y) (a : Fin A) (b : Fin B)
            → (PathP (λ i → Fin (p i)) a b)
            → PathP (λ i → Fin (q i)) (f a) (g b)
  pointwise p q a b r =
    let H = transport-filler (λ i → Fin (p i)) a
    in {!!}
  -- pointwise p q a b r = subst (λ ○ → PathP (λ i → Fin (q i)) (f a) (g ○))
  --                             {!r!} {!!}

  
  -- pointwise {A} {B} p fzero fzero = {!cong (λ ○ → ○ fzero) {!path i!}!}
  -- pointwise p fzero (fsuc b) = absurd (fzero≢fsuc b {!!})
  -- pointwise p (fsuc a) fzero = {!!}
  -- pointwise p (fsuc a) (fsuc b) = {!!}
  
   
-- module _ where
--   swap-eq : swap ≈ swap'
--   p = sym (+-zero 2)
--   q = sym (+-zero 2)
--   pointwise : {m : ℕ} → (x : Fin m) → PathP (λ z → Fin (q z)) (swap x) (swap' x)
--   pointwise fzero = reflλ i → 
--   pointwise (fsuc x) = cong {!!} {!pointwise x!}
--   s : PathP (λ i → MapPath p q i) swap swap'  
--   s = funExt {!!} 
--   swap-eq = record
--     { p = p
--     ; q = q
--     ; path = transport-filler (λ j → {!MapPath p q j!}) swap {!!}
--     }
  

-- pred≈pred' : ∀ {m : ℕ} → pred ≈ pred'
-- pred≈pred' {m} .fst = sym (+-zero (suc (suc m)))
-- pred≈pred' {m} .snd .fst = sym (+-zero (suc m))
--   pred≈pred' {m} .snd .snd fzero = transport-filler {!!} {!!} {!!}
-- pred≈pred' {m} .snd .snd (fsuc a) = {!!}

--   --   sym (+-zero (suc (suc m)))
--   -- , sym (+-zero (suc m))
--   -- , λ a → {!!}
