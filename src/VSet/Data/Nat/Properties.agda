module VSet.Data.Nat.Properties where

open import VSet.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

pred∘suc≡id : (n : ℕ) → predℕ (suc n) ≡ n
pred∘suc≡id zero = refl
pred∘suc≡id (suc n) = cong suc (pred∘suc≡id n)

suc∘predℕ≡id : (n : ℕ) → suc (predℕ (suc n)) ≡ suc n
suc∘predℕ≡id n = cong suc (pred∘suc≡id n)

cong-inj-suc : {X Y : ℕ} (p : suc X ≡ suc Y)
             → Square (λ i → suc X) (λ i → suc Y) (cong (suc ∘ predℕ) p) p
cong-inj-suc {X} {Y} p =
  compPath→Square {p = cong (suc ∘ predℕ) p} {q = p} {r = λ i → suc X} {s = λ i → suc Y}
                  {!!}
  where
    
    R : ℕ → Type
    R zero = ⊥
    R (suc W) = {!!}

x≮0 : (x : ℕ) → ¬ x < 0
x≮0 x (y , y+x'≡0) = snotz (+-comm (suc x) y ∙ y+x'≡0)

