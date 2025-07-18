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
    path : (λ i → MapPath p q i) [ f ≡ g ]
    -- path : subst2 FinFun p q f ≡ g

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


≈sym-pi : ∀ {A B X Y : ℕ} (f : Fin A → Fin X) (g : Fin B → Fin Y) → f ≈ g → g ≈ f
≈⁻∘≈ : ∀ {A B X Y : ℕ} (f : Fin A → Fin X) (g : Fin B → Fin Y)
  → (f≈g : f ≈ g) → {!≈sym f≈g ∘≈ f≈g ≡ id!}

module Trans {A B C X Y Z : ℕ}
           (f : Fin A → Fin X)
           (g : Fin B → Fin Y)
           (h : Fin C → Fin Z)
           (f≈g : f ≈ g) (g≈h : g ≈ h) where

  open _≈_ f≈g renaming (p to p1; q to q1; path to path1)
  open _≈_ g≈h renaming (p to p2; q to q2; path to path2)
  r1 : FinFun A X ≡ FinFun B Y
  r1 i = FinFun (p1 i) (q1 i)
  r2 : FinFun B Y ≡ FinFun C Z
  r2 i = FinFun (p2 i) (q2 i)

  shape : (i j : I) → Partial (~ j ∨ i ∨ ~ i) Type
  shape i j (i = i0) = refl (~ j)
  shape i j (i = i1) = r2 j
  shape i j (j = i0) = r1 i

  -- ∘≈ : (f≈g : f ≈ g) (g≈h : g ≈ h)
  --    → f ≈ h
  -- ∘≈ f≈g g≈h = let
  --   J' = J {x = g}  (λ g' g≡g' → f ≈ g')  f≈g {y = h} {!!}
  --   in {!!}

  -- record
  --   { p = p1 ∙ p2
  --   ; q = q1 ∙ q2
  --   ; path = 
  --   }


  -- path' : MapPath (p1 ∙ p2) (q1 ∙ q2)
  -- path' i = {!!}

  -- shape' : (i j : I) →  Partial {!!} (Fin ((p1 ∙ p2) {!i!}))
  -- shape' i j (j = i0) = {!f x!}
  -- shape' i j (j = i1) = {!!}
  -- shape' i j (i = i0) = {!!}
  -- shape' i j (i = i1) = {!!}

  -- path : PathP (λ i → MapPath (p1 ∙ p2) (q1 ∙ q2) i) f h
  -- path i x = fill (λ j → Fin ((p1 ∙ p2) j)) {!!} {!!} {!!}
  -- -- (Fin ((p1 ∙ p2) i) → Fin ((q1 ∙ q2) i))
  -- -- path i = hfill (λ j p → {!shape i j!}) {!!} (i ∨ ~ i)

  transpTrans : ∀ {ℓ} {A B C : Type ℓ} → (p : A ≡ B) → (q : B ≡ C) → (a : A)
              → transport (p ∙ q) a ≡ transport q (transport p a)
  transpTrans {ℓ} {A} {B} {C} p q a i = hfill (λ j is1 → {!!}) {!!} {!!}

  rect : ∀ (a : Fin A) → subst Fin (q1 ∙ q2) (f a) ≡ h (subst Fin (p1 ∙ p2) a)
  rect a =
    subst Fin (q1 ∙ q2) (f a)
      ≡⟨ refl ⟩
    transport (λ i → Fin ((q1 ∙ q2) i)) (f a)
      ≡⟨ cong (λ ○ → transport ○ (f a)) refl ⟩
    transport (λ i → Fin (((λ i → q1 i) ∙ (λ i → q2 i)) i)) (f a)
      ≡⟨ cong (λ ○ → transport ○ (f a)) refl ⟩
    transport (λ i → (((λ i → Fin (q1 i)) ∙ (λ i → Fin (q2 i))) i)) (f a)
      ≡⟨ cong (λ ○ → transport ○ (f a)) refl ⟩
    transport ((λ i → Fin (q1 i)) ∙ (λ i → Fin (q2 i))) (f a)
      ≡⟨ {!!} ⟩
    transport (λ i → Fin (q2 i)) (transport (λ i → Fin (q1 i)) (f a))
      ≡⟨ {!!} ⟩
    subst Fin q2 (subst Fin q1 (f a))
      ≡⟨ {!!} ⟩
    h (subst Fin (p1 ∙ p2) a) ∎

  path3 : r1 ∙ r2 ≡ (λ i → MapPath (p1 ∙ p2) (q1 ∙ q2) i)
  path3 =
    r1 ∙ r2
      ≡⟨ refl ⟩
    (λ i → MapPath p1 q1 i) ∙ (λ i → MapPath p2 q2 i)
      ≡⟨ refl ⟩
    (λ i → Fin (p1 i) → Fin (q1 i)) ∙ (λ i → Fin (p2 i) → Fin (q2 i))
      ≡⟨ {!!} ⟩
    (λ i → Fin ((p1 ∙ p2) i) → Fin ((q1 ∙ q2) i))
      ≡⟨ refl ⟩
    (λ i → MapPath (p1 ∙ p2) (q1 ∙ q2) i) ∎

  module _ {A B C X Y Z : Type} (F : Type → Type → Type)
           (f : F A X) (g : F B Y) (h : F C Z)
           {a : A} {c : C} {x : X} {z : Z}
           (p1 : A ≡ B) (p2 : B ≡ C) (q1 : X ≡ Y) (q2 : Y ≡ Z) where
    path4 : (λ i → F (p1 i) (q1 i)) ∙ (λ i → F (p2 i) (q2 i))
          ≡ (λ i → F ((p1 ∙ p2) i) ((q1 ∙ q2) i))
    path4 =
      J {!!} {!!} {!!} 
      (λ i → F (p1 i) (q1 i)) ∙ (λ i → F (p2 i) (q2 i))
        ≡⟨ (congP₂ {A = λ i → (p1 ∙ p2) i} {B = λ i _ → (q1 ∙ q2) i}
                   {C = λ i a b → {!F a b!}} (λ i a b → {!!})
                   {x = a} {y = c} {u = x} {v = z}
                   {!λ i → transport (λ j → (p1 ∙ p2) {!j!}) {!!}!} {!!} ∙₂ {!!}) i0 ⟩
      (λ i → F ((p1 ∙ p2) i) ((q1 ∙ q2) i)) ∎

    path5 : (λ i → F (p1 i) (q1 i)) ∙ (λ i → F (p2 i) (q2 i))
          ≡ (λ i → F ((p1 ∙ p2) i) ((q1 ∙ q2) i))
    path5 =
      J-∙ {x = g} (λ f' g≡f → {!g ≈ f!}) {!!} {!!} {!!} 

  ≈trans : f ≈ g → g ≈ h → f ≈ h
  ≈trans f≈g g≈h = record
    { p = p1 ∙ p2
    ; q = q1 ∙ q2
    ; path = {!r1 ∙ r2!}
    }


{-
constPath≡refl : {B : Type} → toPathP (λ _ → B) ≡ refl {x = B}
constPath≡refl {B} =
  toPathP {A = λ _ → Type} {x = B} {y = B} (λ _ → B) ≡⟨ refl ⟩
  (λ i → hcomp (λ j → λ { (i = i0) → B
                        ; (i = i1) → (λ _ → B) j })
              (transp (λ j → (λ _ → Type) (i ∧ j)) (~ i) B)) ≡⟨ refl ⟩
  (λ i → hcomp (λ _ _ → B)
              (transp (λ _ → Type) (~ i) B)) ≡⟨ refl ⟩
  refl ∎


-- transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
--                    → PathP (λ i → p i) x (transport p x)
-- transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

transpRefl : {A : Type} → (x : A) → transport (λ _ → A) x ≡ x
-- transpRefl x = transport-filler refl {!!} {!!}
transpRefl {A} x =
  transport (λ _ → A) x ≡⟨ cong (λ ○ → transport ○ x) refl i1 ⟩
  transport refl x ≡⟨ transportRefl x ⟩
  x ∎

≈refl : {A X : ℕ} (f : Fin A → Fin X) → f ≈ f
≈refl {A} {X} f = record
  { p = refl
  ; q = refl
  ; path = transpRefl f
  }

≈sym : ∀ {A B X Y : ℕ} (f : Fin A → Fin X) (g : Fin B → Fin Y) → f ≈ g → g ≈ f
≈sym {A} {B} {X} {Y} f g f≈g = record
  { p = sym p 
  ; q = sym q
  ; path = path'
  }
  where
    open _≈_ f≈g
    r : FinFun A X ≡ FinFun B Y
    r i = FinFun (p i) (q i)
    path' : subst2 FinFun (sym p) (sym q) g ≡ f
    path' =
      subst2 FinFun (sym p) (sym q) g ≡⟨ refl ⟩
      transport⁻ r g ≡⟨ cong (transport (sym r)) (sym path) ⟩
      transport⁻ r (transport r f) ≡⟨ transport⁻Transport r f ⟩
      f ∎


module Trans {A B C X Y Z : ℕ}
           (f : Fin A → Fin X)
           (g : Fin B → Fin Y)
           (h : Fin C → Fin Z)
           (f≈g : f ≈ g) (g≈h : g ≈ h) where

  open _≈_ f≈g renaming (p to p1; q to q1; path to path1)
  open _≈_ g≈h renaming (p to p2; q to q2; path to path2)
  r1 : FinFun A X ≡ FinFun B Y
  r1 i = FinFun (p1 i) (q1 i)
  r2 : FinFun B Y ≡ FinFun C Z
  r2 i = FinFun (p2 i) (q2 i)

  term1 : (i : I) (j : I) → Partial (i ∨ ~ i) Type
  term1 i j (i = i0) = refl (~ j)
  term1 i j (i = i1) = FinFun (p2 j) (q2 j)

  lemma1 : (λ i → FinFun ((p1 ∙ p2) i) ((q1 ∙ q2) i))
         ≡ (λ i → FinFun (p1 i) (q1 i)) ∙ (λ i → FinFun (p2 i) (q2 i)) 
  lemma1 =
    (λ i → FinFun ((p1 ∙ p2) i) ((q1 ∙ q2) i)) ≡⟨ {!!} ⟩
    (λ i → hcomp (term1 i)
                 (FinFun (p1 i) (q1 i))) ≡⟨ refl ⟩
    (λ i → hcomp (doubleComp-faces refl (λ i → FinFun (p2 i) (q2 i)) i)
                 (FinFun (p1 i) (q1 i))) ≡⟨ refl ⟩
    refl ∙∙ (λ i → FinFun (p1 i) (q1 i)) ∙∙ (λ i → FinFun (p2 i) (q2 i)) ≡⟨ refl ⟩
    (λ i → FinFun (p1 i) (q1 i)) ∙ (λ i → FinFun (p2 i) (q2 i)) ∎

  ≈trans : f ≈ g → g ≈ h → f ≈ h
  ≈trans f≈g g≈h = record
    { p = p1 ∙ p2
    ; q = q1 ∙ q2
    ; path = path'
    }
    where
      path' : subst2 FinFun (p1 ∙ p2) (q1 ∙ q2) f ≡ h
      path' =
        subst2 FinFun (p1 ∙ p2) (q1 ∙ q2) f ≡⟨ refl ⟩
        transport (λ i → FinFun ((p1 ∙ p2) i) ((q1 ∙ q2) i)) f
          ≡⟨ {!refl!} ⟩
        transport ((λ i → FinFun (p1 i) (q1 i)) ∙ (λ i → FinFun (p2 i) (q2 i))) f
          ≡⟨ {!!} ⟩
        transport ((λ i → FinFun (p1 i) (q1 i)) ∙ (λ i → FinFun (p2 i) (q2 i))) f
          ≡⟨ {!!} ⟩
        transport (r1 ∙ r2) f
          ≡⟨ {!!} ⟩
        h ∎

      -- transport (λ i → FinFun ((refl ∙∙ p1 ∙∙ p2) i) ((refl ∙∙ q1 ∙∙ q2) i)) f ≡⟨ {!!} ⟩
      -- transport (λ i → FinFun (hcomp (doubleComp-faces refl p2 i) (p1 i))
      --                         (hcomp (doubleComp-faces refl q2 i) (q1 i))) f ≡⟨ {!refl!} ⟩
      -- transport (λ i → FinFun (hcomp (doubleComp-faces refl p2 i) (p1 i))
      --                         (hcomp (doubleComp-faces refl q2 i) (q1 i))) f ≡⟨ {!refl!} ⟩

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

  -- pointwise : {A B X Y : ℕ} (p : A ≡ B) (q : X ≡ Y) (a : Fin A) (b : Fin B)
  --           → (PathP (λ i → Fin (p i)) a b)
  --           → PathP (λ i → Fin (q i)) (f a) (g b)
  -- pointwise p q a b r =
  --   let H = transport-filler (λ i → Fin (p i)) a
  --   in {!!}
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
-}
