module VSet.Data.Fin.SumSplit where

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.Fin.Base
open import Cubical.Data.Nat

open Iso

⊎→+ : ∀ (X Y : ℕ) → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ X + Y ⟧
⊎→+ X Y (inl a) = finject Y a
⊎→+ X Y (inr a) = fshift X a

inc : ∀ (X Y : ℕ) → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ suc X ⟧ ⊎ ⟦ Y ⟧
inc X Y (inl a) = inl (fsuc a)
inc X Y (inr a) = inr a

+→⊎ : ∀ (X Y : ℕ) → ⟦ X + Y ⟧ → ⟦ X ⟧ ⊎ ⟦ Y ⟧
+→⊎ zero Y a = inr a
+→⊎ (suc X) Y fzero = inl fzero
+→⊎ (suc X) Y (fsuc a) = inc X Y (+→⊎ X Y a)

+→⊎-X-0≡inl : (X : ℕ) (a : ⟦ X + 0 ⟧)
            → +→⊎ X 0 a ≡ inl (subst Fin (+-zero X) a)
+→⊎-X-0≡inl (suc X) fzero = cong inl (fzero≡subst-fzero (+-zero X))
+→⊎-X-0≡inl (suc X) (fsuc a) =
  +→⊎ (suc X) 0 (fsuc a)
    ≡⟨ refl ⟩
  inc X 0 (+→⊎ X 0 a)
    ≡⟨ cong (inc X 0) (+→⊎-X-0≡inl X a) ⟩
  inc X 0 (inl (subst Fin (+-zero X) a))
    ≡⟨ refl ⟩
  inl (fsuc (subst Fin (+-zero X) a))
    ≡⟨ cong inl (sym (subst-fsuc-reorder (+-zero X) a)) ⟩
  inl (subst Fin (+-zero (suc X)) (fsuc a)) ▯

⊎→+-inc : ∀ (X Y : ℕ) (z : ⟦ X ⟧ ⊎ ⟦ Y ⟧)
        → ⊎→+ (suc X) Y (inc X Y z) ≡ fsuc (⊎→+ X Y z)
⊎→+-inc X Y (inl a) = finject-fsuc-reorder a
⊎→+-inc X Y (inr a) = refl

sect : ∀ (X Y : ℕ) → section {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} (⊎→+ X Y) (+→⊎ X Y)
sect zero Y a = refl
sect (suc X) zero fzero = refl
sect (suc X) (suc Y) fzero = refl
sect (suc X) zero (fsuc a) =
  ⊎→+ (suc X) zero (+→⊎ (suc X) zero (fsuc a))
    ≡⟨ cong (⊎→+ (suc X) 0) (+→⊎-X-0≡inl (suc X) (fsuc a)) ⟩
  ⊎→+ (suc X) zero (inl (subst Fin (+-zero (suc X)) (fsuc a)))
    ≡⟨ refl ⟩
  finject zero (subst Fin (+-zero (suc X)) (fsuc a))
    ≡⟨ finject0≡subst ((subst Fin (+-zero (suc X)) (fsuc a))) ⟩
  subst Fin (sym (+-zero (suc X))) (subst Fin (+-zero (suc X)) (fsuc a))
    ≡⟨ subst⁻Subst Fin (+-zero (suc X)) (fsuc a) ⟩
  fsuc a ▯
sect (suc X) (suc Y) (fsuc a) =
  ⊎→+ (suc X) (suc Y) (+→⊎ (suc X) (suc Y) (fsuc a))
    ≡⟨ refl ⟩
  ⊎→+ (suc X) (suc Y) (inc X (suc Y) (+→⊎ X (suc Y) a))
    ≡⟨ ⊎→+-inc X (suc Y) (+→⊎ X (suc Y) a) ⟩
  fsuc (⊎→+ X (suc Y) (+→⊎ X (suc Y) a)) 
    ≡⟨ cong fsuc (sect X (suc Y) a) ⟩
  fsuc a ▯

retr : ∀ (X Y : ℕ) → retract {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} (⊎→+ X Y) (+→⊎ X Y)
retr zero Y (inr a) = refl
retr (suc X) Y (inl fzero) =
  +→⊎ (suc X) Y (⊎→+ (suc X) Y (inl fzero))
    ≡⟨ refl ⟩
  +→⊎ (suc X) Y (finject Y fzero)
    ≡⟨ refl ⟩
  +→⊎ (suc X) Y fzero
    ≡⟨ refl ⟩
  inl fzero ▯
retr (suc X) zero (inl (fsuc a)) =
  +→⊎ (suc X) zero (⊎→+ (suc X) zero (inl (fsuc a))) ≡⟨ refl ⟩
  +→⊎ (suc X) zero (finject 0 (fsuc a)) ≡⟨ refl ⟩
  +→⊎ (suc X) zero (fsuc (finject 0 a)) ≡⟨ refl ⟩
  inc X zero (+→⊎ X zero (finject 0 a)) ≡⟨ refl ⟩
  inc X zero (+→⊎ X zero (⊎→+ X zero (inl a)))
    ≡⟨ cong (inc X zero) (retr X zero (inl a)) ⟩
  inl (fsuc a) ▯
retr (suc X) (suc Y) (inl (fsuc a)) =
  +→⊎ (suc X) (suc Y) (⊎→+ (suc X) (suc Y) (inl (fsuc a))) ≡⟨ refl ⟩
  +→⊎ (suc X) (suc Y) (finject {x = suc X} (suc Y) (fsuc a)) ≡⟨ refl ⟩
  +→⊎ (suc X) (suc Y) (fsuc (finject {x = X} (suc Y) a)) ≡⟨ refl ⟩
  +→⊎ (suc X) (suc Y) (fsuc (finject {X} (suc Y) a)) ≡⟨ refl ⟩
  inc X (suc Y) (+→⊎ X (suc Y) (finject {X} (suc Y) a)) ≡⟨ refl ⟩
  inc X (suc Y) (+→⊎ X (suc Y) (⊎→+ X (suc Y) (inl a)))
    ≡⟨ cong (inc X (suc Y) ) (retr X (suc Y) (inl a)) ⟩
  inc X (suc Y) (inl a) ≡⟨ refl ⟩
  inl (fsuc a) ▯
retr (suc X) Y (inr a) =
  +→⊎ (suc X) Y (⊎→+ (suc X) Y (inr a)) ≡⟨ refl ⟩
  +→⊎ (suc X) Y (fshift (suc X) a) ≡⟨ refl ⟩
  +→⊎ (suc X) Y (fsuc (fshift X a)) ≡⟨ refl ⟩
  inc X Y (+→⊎ X Y (fshift X a)) ≡⟨ refl ⟩
  inc X Y (+→⊎ X Y (⊎→+ X Y (inr a))) ≡⟨ cong (inc X Y) (retr X Y (inr a)) ⟩
  inc X Y (inr a) ≡⟨ refl ⟩
  inr a ▯

⊎↔+ : ∀ (X Y : ℕ) → Iso (⟦ X ⟧ ⊎ ⟦ Y ⟧) ⟦ X + Y ⟧
⊎↔+ X Y = iso (⊎→+ X Y) (+→⊎ X Y) (sect X Y) (retr X Y)

{-
split : ∀ (X Y : ℕ) → (u : ⟦ X +ℕ Y ⟧)
      → (Σ[ x ∈ ⟦ X ⟧ ] ⊎→+ X Y (inl x) ≡ u)
      ⊎ (Σ[ y ∈ ⟦ Y ⟧ ] ⊎→+ X Y (inr y) ≡ u)
split X Y u with +→⊎ X Y u | inspect (+→⊎ X Y) u 
... | inl x | [ path ]ᵢ = {!!}

-- eq : u ≡ finject Y x
-- eq =
--   u ≡⟨ sym (sect {X = W} u) ⟩
--   ⊎→+ {X = W} {Y = Y} (+→⊎ {X = W} u) ≡⟨ cong ⊎→+ path ⟩
--   ⊎→+ {X = W} {Y = Y} (inl x) ≡⟨ cong (⊎→+ {X = W} {Y = Y}) (sym (retr {X = W} {Y = Y} (inl x))) ⟩
--   ⊎→+ {X = W} (+→⊎ {X = W} (⊎→+ {X = W} (inl x))) ≡⟨ refl ⟩ 
--   ⊎→+ (+→⊎ (finject Y x)) ≡⟨ sect (finject Y x) ⟩
--   finject Y x ▯
-- -}
-- -}
-- -}
