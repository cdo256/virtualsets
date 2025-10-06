module VSet.Data.Nat.Order where

open import VSet.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order public

private
  variable
    ℓ : Level

pred∘suc : (n : ℕ) → predℕ (suc n) ≡ n
pred∘suc n = refl

0<suc : ∀ (n : ℕ) → 0 < suc n
0<suc n = n , +-comm n 1

pred-<-pred : ∀ {m n : ℕ} → suc m < suc n → m < n 
pred-<-pred {m} {n} (k , k+m''≡n') = k , k+m'≡n
  where
    k+m'≡n : k + suc m ≡ n
    k+m'≡n =
      k + suc m ≡⟨ +-comm k (suc m) ⟩
      suc m + k ≡⟨ refl ⟩
      suc (m + k) ≡⟨ pred∘suc (suc (m + k)) ⟩
      predℕ (suc (suc (m + k))) ≡⟨ refl ⟩
      predℕ (suc (suc m) + k) ≡⟨ cong predℕ (+-comm (suc (suc m)) k) ⟩
      predℕ (k + suc (suc m) ) ≡⟨ cong predℕ k+m''≡n' ⟩
      predℕ (suc n) ≡⟨ pred∘suc n ⟩
      n ▯

suc-<-suc : ∀ {m n : ℕ} → m < n → suc m < suc n
suc-<-suc {m} {n} (k , k+m'≡n) = k , k+m''≡n'
  where
    k+m''≡n' : k + suc (suc m) ≡ suc n
    k+m''≡n' =
      k + suc (suc m) ≡⟨ +-comm k (suc (suc m)) ⟩
      suc (suc m) + k  ≡⟨ cong suc (+-comm (suc m) k ∙ k+m'≡n) ⟩
      suc n ▯

suc≥1 : (x : ℕ) → suc x ≥ 1
suc≥1 x = x , +-comm x 1

0≱y+1 : (x : ℕ) → ¬ 0 ≥ x + 1
0≱y+1 x (y , y+x+1≡0) = snotz s≡0
  where
    s≡0 : suc (y + x) ≡ 0
    s≡0 = suc (y + x) ≡⟨ +-comm 1 (y + x) ⟩
          (y + x) + 1 ≡⟨ sym (+-assoc y x 1) ⟩
          y + (x + 1) ≡⟨ y+x+1≡0 ⟩
          0 ▯

0≱1 : ¬ 0 ≥ 1
0≱1 (x , x+1≡0) = snotz (+-comm 1 x ∙ x+1≡0)

0≱suc : (x : ℕ) → ¬ 0 ≥ suc x
0≱suc x (k , k+x'≡0) = snotz (+-comm (suc x) k ∙ k+x'≡0)

≢0→≥1 : (x : ℕ) → x ≢ 0 → x ≥ 1
≢0→≥1 zero 0≢0 = absurd (0≢0 refl)
≢0→≥1 (suc x) x≢0 = suc≥1 x

≤∧≥→≡ : {m n : ℕ} → m ≤ n → m ≥ n → m ≡ n
≤∧≥→≡ {zero} {zero} m≤n m≥n = refl
≤∧≥→≡ {zero} {suc n} m≤n m≥n = absurd (¬-<-suc m≥n (suc-≤-suc zero-≤))
≤∧≥→≡ {suc m} {zero} m≤n m≥n = absurd (¬-<-suc m≤n (suc-≤-suc zero-≤))
≤∧≥→≡ {suc m} {suc n} m≤n m≥n = cong suc (≤∧≥→≡ (pred-≤-pred m≤n) (pred-≤-pred m≥n))
