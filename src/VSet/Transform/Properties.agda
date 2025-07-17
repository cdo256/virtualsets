module VSet.Transform.Properties where

open import VSet.Prelude
open import VSet.Data.Fin hiding (pred)

open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Data.SomeFin.Equality
open import VSet.Transform.Sub
open import VSet.Transform.Tensor
open import VSet.Transform.Split using (⊎↔+; ⊎→+; +→⊎)
open import VSet.Transform.Pred

open import Cubical.Data.Nat.Properties

𝟘⊕≡id : ∀ {X Y : SomeFin} → (f : [ X ↣ Y ]) → 𝟘 ⊕ f ≈ f
𝟘⊕≡id {X} {Y} f = record
  { p = refl
  ; q = refl
  -- Goal: (λ i → cong₂ FinFun (λ _ → 0 + X) (λ _ → 0 + Y) i) [
  --   fst (𝟘 ⊕ f) ≡ fst f ]
  ; path = cong (λ ○ x → fst f x) (refl {x = f})
  }

step3 : ∀ {X Y : SomeFin} → (f : [ X ↣ Y ]) 
      → (x : Fin (X + 0)) → subst Fin (sym (+-zero Y)) (fst f (subst Fin (+-zero X) x)) 
      ≡ ⊎→+ (⊎-map (fst f) (fst 𝟘) (+→⊎ x))  
step3 {suc X} {Y} f fzero =
  subst Fin (sym (+-zero Y)) (fst f (subst Fin (+-zero (suc X)) fzero)) 
    ≡⟨ congP (λ i ○ → subst Fin (sym (+-zero Y)) (fst f ○))
    -- Goal: subst Fin (λ i → suc (+-zero X i)) fzero ≡ fzero
              {!!} ⟩
  subst Fin (sym (+-zero Y)) (fst f fzero) 
    ≡⟨ {!cong !} ⟩
  {!!}
    ≡⟨ {!!} ⟩
  ⊎→+ (⊎-map (fst f) (fst 𝟘) (+→⊎ fzero)) ▯
  where
    step4 : (λ i → Fin (+-zero (suc X) i)) [ fzero ≡ subst Fin (+-zero (suc X)) fzero ]
    step4 = subst-filler Fin (+-zero (suc X)) fzero
step3 {suc X} f (fsuc x) = {!!}


⊕𝟘≡id : ∀ {X Y : SomeFin} → (f : [ X ↣ Y ]) → f ⊕ 𝟘 ≈ f
⊕𝟘≡id {X} {Y} f =
  ≈sym {!!}
  where
    t : [ (X + 0) ↣ (Y + 0) ]
    t = ≈transport (λ i → +-zero X (~ i)) (λ i → +-zero Y (~ i)) f 
    step1 : f ≈ t
    step1 = ≈cong (sym (+-zero X)) (sym (+-zero Y)) f
    open _≈_ step1
    step2 : t ≈ f ⊕ 𝟘
    step2 = record
      { p = refl
      ; q = refl
      ; path = funExt (λ x → 
          fst t x ≡⟨ refl ⟩
          subst Fin q (fst f (subst Fin (sym p) x))
            ≡⟨ subst2-filler {!FinFun!} {!!} {!!} {!!} ⟩
          ⊎→+ (⊎-map (fst f) (fst 𝟘) (inl (subst Fin ((+-zero X)) x)))
            ≡⟨ {!!} ⟩
          ⊎→+ (⊎-map (fst f) (fst 𝟘) (+→⊎ x))
            ≡⟨ refl ⟩
          fst (↔to↣ ⊎↔+ ↣∘↣ ↣-map-⊎ f 𝟘 ↣∘↣ ↔to↣ (flip-↔ ⊎↔+)) x
            ≡⟨ refl ⟩
          fst (f ⊕ 𝟘) x ▯)
      }
    
    -- -f⊕𝟘
-- record
--   { p = +-zero X
--   ; q = +-zero Y
--   -- Goal: (λ i → cong₂ FinFun (+-zero X) (+-zero Y) i) [ fst (f ⊕ 𝟘) ≡
--   --  fst f ]
--   ; path = λ i x → c2 {!!} {!!}
--   }
--   where
--     f' : [ X + 0 ↣ Y + 0 ]
--     f' = f ⊕ 𝟘
--     -- c2 : ? [ FinFun X Y ≡ FinFun (X + 0) (Y + 0) ]
--     c2 : (i : I) → cong₂ FinFun (+-zero X) (+-zero Y) i
--     c2 i x = y
--       where
--         x' : Fin X
--         x' = transport (λ j → Fin (+-zero X (i ∨ j))) x
--         y' : Fin Y
--         y' = fst f x'
--         y : Fin (+-zero Y i)
--         y = transport⁻ (λ j → Fin (+-zero Y (i ∨ j))) y'
      
    
-- 𝟘⊕≈id {X} {Y} f x = 
--   fst (𝟘 ⊕ f) x ≡⟨ refl ⟩
--   fst (↔to↣ ⊎↔+ ↣∘↣ ↣-map-⊎ 𝟘 f ↣∘↣ ↔to↣ (flip-↔ ⊎↔+)) x ≡⟨ refl ⟩
--   (fst (↔to↣ ⊎↔+) ∘ fst (↣-map-⊎ 𝟘 f) ∘ fst (↔to↣ (flip-↔ ⊎↔+))) x ≡⟨ refl ⟩
--   ⊎→+ (⊎-map (λ ()) (fst f) (+→⊎ x)) ≡⟨ refl ⟩
--   ⊎→+ (inr (fst f x)) ≡⟨ refl ⟩
--   fst f x ▯

{-
finPath : (n : ℕ) → Fin n ≡ Fin (n + 0)
finPath n = cong Fin (sym (+-zero n))

x1 : Fin 1
x1 = fzero 
refl1 : x1 ≡ x1
refl1 = refl
x2 : Fin (1 + 0)
x2 = fzero

q = subst Fin (+-zero 1) x2

r : Fin 1 ≡ Fin (1 + 0)
r = subst (λ ○ → Fin ○ ≡ Fin (○ + 0)) (+-zero 1) (cong Fin (sym (+-zero 1)))

w : ∀ {m : ℕ} → fzero {n = m} ≡ subst Fin (cong suc (+-zero m)) (fzero {n = m + 0})
w {m} = transport (cong (λ ○ → fzero {n = m} ≡ Fin {!suc ○!} ) {!!}) {!!} {!!}

foo : ∀ (n m : ℕ) → (f : Fin n → Fin m) → (g : Fin (n + 0) → Fin (m + 0)) → Type
foo n m f g = PathP (λ i → (x : Fin n) → (Fin (m + 0)))
  (g ∘ subst Fin (sym (+-zero n))) 
  (subst Fin (sym (+-zero m)) ∘ f)



-- ⊕𝟘≈id : ∀ {X Y : SomeFin} → (f : [ X ↣ Y ]) → f ⊕ 𝟘 ≈ f
-- ⊕𝟘≈id {X} {Y} f x =  ?
--   -- fst (f ⊕ 𝟘) x ≡⟨ refl ⟩
  -- fst (↔to↣ ⊎↔+ ↣∘↣ ↣-map-⊎ f 𝟘 ↣∘↣ ↔to↣ (flip-↔ ⊎↔+)) x ≡⟨ refl ⟩
  -- (fst (↔to↣ ⊎↔+) ∘ fst (↣-map-⊎ f 𝟘) ∘ fst (↔to↣ (flip-↔ ⊎↔+))) x ≡⟨ refl ⟩
  -- ⊎→+ (⊎-map (λ ()) (fst f) {!+→⊎ x!}) ≡⟨ refl ⟩
  -- ⊎→+ (inl (fst f x)) ≡⟨ refl ⟩
  -- fst f x ▯

lemma1-3 : ∀ (X Y A : SomeFin) → (f : [ X ↣ Y ])
         → sub A (ladd A f) ≈ f
lemma1-3 X Y zero f = {!!}
lemma1-3 X Y (suc A) f =
  {!!}

lemma1-4 : ∀ (X Y A B : SomeFin) → (f : [ A + X ↣ A + Y ])
         → radd B (sub A f) ≈ sub A {!add B f!} 

-- -}
-- -}
-- -}
-- -}
-- -}
