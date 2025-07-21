module VSet.Data.Nat.Properties where

open import VSet.Prelude
open import Cubical.Data.Nat

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
  -- hfill (λ { j (i = i0) → refl
  --          ; j (i = i1) → refl })
  --       {!!} {!!}
  where
    
    R : ℕ → Type
    R zero = ⊥
    R (suc W) = {!!}
  -- case p i of λ
  --   { zero → {!!}
  --   ; (suc b) → absurd {!!}
  --   }

{-

-- ∨ - max
-- ∧ - min
... | zero = absurd (snotz λ j → {!p (j ∧ i)!})
... | suc W = {!!}
  -- cong suc (injSuc p) i
  --   ≡⟨ refl ⟩
  -- suc (injSuc p i)
  --   ≡⟨ {!refl!} ⟩
  -- p i ▯


  -- cong suc (injSuc p)
  --   ≡⟨ refl ⟩
  -- cong suc (cong predℕ p)
  --   ≡⟨ refl ⟩
  -- (λ i → suc (predℕ (p i)))
  --   ≡⟨ {!!} ⟩
  -- p ▯
-- -}
