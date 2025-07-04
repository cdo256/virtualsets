module VSet.Transform.Split where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Sum.Properties
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Properties
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Pred

swap : ∀ {A B} → ⟦ A + B ⟧ ↔ ⟦ B + A ⟧
swap = {!(flip-↔ +↔⊎) ↔∘↔ {!⊎-swap-↔!} ↔∘↔ +↔⊎!}

swap-involutive : ∀ {A B : SomeFin} {x} → (swap ↔∘↔ swap) ^ ≡ id
swap-involutive {A} {B} {x} = flip-IsId swap

inl-injective : ∀ {A} {x y : A} → inl x ≡ inl y → x ≡ y
inl-injective refl = {!!}
inr-injective : ∀ {A} {x y : A} → inr x ≡ inr y → x ≡ y
inr-injective refl = {!!}

map↣⊎ : ∀ {A B C D} → (A ↣ B) → (C ↣ D) → ((A ⊎ C) ↣ (B ⊎ D))
map↣⊎ {A} {B} {C} {D} f g = {!!}
-- record
--   { fst = h
--   ; cong = cong h
--   ; injective = inj
--   }
--   where open Injection
--       h : (A ⊎ C) → (B ⊎ D)
--       h (inl a) = inl (fst f a)
--       h (inr c) = inr (fst g c)
--       inj : ∀ {x y} → h x ≡ h y → x ≡ y
--       inj {inl x} {inl y} =
--         cong inl ∘ injective f ∘ inl-injective
--       inj {inr x} {inr y} =
--         cong inr ∘ injective g ∘ inr-injective

⊎⊥ˡ : ∀ {A} → (A ⊎ ⟦ zero ⟧) ↔ A
⊎⊥ˡ = {!!}
-- ⊎⊥ˡ {A} = record
--   { fst = f
--   ; from = inl
--   ; to-cong = f-cong
--   ; from-cong = cong inl
--   ; inverse = invˡ , invʳ
--   }
--   where
--     f : (A ⊎ ⟦ zero ⟧) → A
--     f (inl x) = x 
--     f-cong : {x' y' : A ⊎ ⟦ zero ⟧} → x' ≡ y' → f x' ≡ f y' 
--     f-cong {inl x} {inl y} = inl-injective
--     invˡ : ∀ {x} {y} → y ≡ inl x → f y ≡ x
--     invˡ {x} {inl y} = inl-injective
--     invʳ : ∀ {x} {y} → y ≡ f x → inl y ≡ x
--     invʳ {inl x} {y} = cong inl

⊎⊥ʳ : ∀ {A} → (⟦ zero ⟧ ⊎ A) ↔ A
⊎⊥ʳ {A} = record
  { to = f
  ; from = inr
  ; to-cong = f-cong
  ; from-cong = cong inr
  ; inverse = invˡ , invʳ
  }
  where
    f : (⟦ zero ⟧ ⊎ A) → A
    f (inr x) = x 
    f-cong : {x' y' : ⟦ zero ⟧ ⊎ A} → x' ≡ y' → f x' ≡ f y' 
    f-cong {inr x} {inr y} = inr-injective
    invˡ : ∀ {x} {y} → y ≡ inr x → f y ≡ x
    invˡ {x} {inr y} = inr-injective
    invʳ : ∀ {x} {y} → y ≡ f x → inr y ≡ x
    invʳ {inr x} {y} = cong inr

splice : {X : SomeFin} → (a : ⟦ suc X ⟧) → ⟦ X ⟧ ↔ (suc X ∖ a)
splice {X} a = record
  { fst = ins a
  ; from = del a 
  ; to-cong = cong (ins a)
  ; from-cong = cong (del a)
  ; inverse = {!!} , {!!}
  }

-- splice-inverseˡ : {X : SomeFin} → (a : ⟦ suc X ⟧) → Inverseˡ (del a) (ins a)
-- splice-inverseˡ {zero} a {()} {y} y≡x+
-- splice-inverseˡ {suc X} fzero {fzero} {fsuc y , y'≢0} y≡x+ = {!!}
-- splice-inverseˡ {suc X} (fsuc a) {fzero} {fzero , 0≢a'} y≡x+ = refl
-- splice-inverseˡ {suc X} fzero {fsuc x} {fsuc (fsuc y) , y≢0} =
--   λ L → ?
-- 
--     -- cong fsuc {!suc-inj (suc-inj (inl-injective!} --  (cong inl {!y≡x+!})
-- splice-inverseˡ {suc X} (fsuc a) {fsuc x} {fsuc y , y'≢a'} y≡x+ = {!!}
--   -- begin
--   --     del a y
--   --   ≡⟨ {!!} ⟩
--   --     x ∎
-- 
-- -- dec : ∀ {X Y : SomeFin} → ((⟦ X ⟧ ⊎ ⟦ 1 ⟧) ↣ (⟦ Y ⟧ ⊎ ⟦ 1 ⟧))
-- --     → (⟦ X ⟧ ↣ ⟦ Y ⟧)
-- -- dec {X} {Y} f = {!!}
-- --     where
-- --       g : ⟦ X ⟧ → ⟦ Y ⟧
-- --       g x = {!!}
-- 
-- _-ᶠ_ : {A' X Y : SomeFin} → (f : (⟦ X ⟧ ⊎ ⟦ A' ⟧) ↣ (⟦ Y ⟧ ⊎ ⟦ A' ⟧))
--     → (A : SomeFin) → {A ≡ A'}
--     → ⟦ X ⟧ ↣ ⟦ Y ⟧
-- _-ᶠ_ {A' = zero} f zero = ↔to↣ ⊎⊥ˡ ↣∘↣ f ↣∘↣ ↔to↣ (flip-↔ ⊎⊥ˡ)
-- _-ᶠ_ {A' = suc A'} {X} {Y} f (suc A) {eq} = _-ᶠ_ {A'} g A 
--   where
--     g : (⟦ X ⟧ ⊎ ⟦ A' ⟧) ↣ (⟦ Y ⟧ ⊎ ⟦ A' ⟧)
--     g = map↣⊎ id↣ {!ins!}  ↣∘↣ f ↣∘↣ map↣⊎ id↣ {!!}
-- 
-- -- _-ᶠ_ {A'} {X} {Y} f A =
-- --   let g = (↔to↣ (swap {Y} {A'})) ↣∘↣ f ↣∘↣ (↔to↣ (swap {A'} {X}))
-- --   in sym-sub g A
-- 
-- 
-- _+ᶠ-sym_ : ∀ {X Y : SomeFin} (g : ⟦ X ⟧ ↣ ⟦ Y ⟧) → (A : SomeFin)
--         → ⟦ X + A ⟧ ↣ ⟦ Y + A ⟧
-- _+ᶠ-sym_ {X} {Y} g A = ↔to↣ (flip-↔ +↔⊎) ↣∘↣ map↣⊎ g (id↣ {⟦ A ⟧}) ↣∘↣ ↔to↣ +↔⊎
-- 
-- _+ᶠ-sym_ : ∀ {X Y : SomeFin} (g : ⟦ X ⟧ ↣ ⟦ Y ⟧) → (A : SomeFin)
--         → ⟦ A + X ⟧ ↣ ⟦ A + Y ⟧
-- _+ᶠ-sym_ {X} {Y} g zero = g
-- _+ᶠ-sym_ {X} {Y} g (suc A) = ↔to↣ (flip-↔ +↔⊎) ↣∘↣ map↣⊎ (id↣ {⟦ 1 ⟧}) (g +ᶠ-sym A) ↣∘↣ ↔to↣ +↔⊎
--   record
--     { fst = g''
--     ; cong = cong g''
--     ; injective = inj
--     }
--     where
--       g' = g +ᶠ-sym A
--       g'' : Fin (suc A + X) → Fin (suc A + Y)
--       g'' fzero = fzero
--       g'' (fsuc a) = fsuc (fst g' a)
--       inj : Injective g''
--       inj {fzero} {fzero} eq = refl
--       inj {fsuc x} {fsuc y} eq =
--         begin
--             fsuc x
--           ≡⟨ cong fsuc (injective g' (suc-inj eq)) ⟩
--             fsuc y ∎
