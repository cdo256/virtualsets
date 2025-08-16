module VSet.Data.Inj.FinFun where

open import VSet.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import VSet.Function.Iso
open import VSet.Function.Injection
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base
open import VSet.Data.Inj.Properties
open import VSet.Data.FinFun.Injection

Inj→FinFun : {m n : ℕ} → Inj m n → [ m ↣ n ]
Inj→FinFun f = apply f , apply-Inj-isInjective f

-- FinFun→m≤n : {m n : ℕ} → [ m ↣ n ] → m ≤ n
-- FinFun→m≤n {zero} {n} f = zero-≤ 
-- FinFun→m≤n {suc m} {zero} (f , _) = Fin0-absurd (f f0)
-- FinFun→m≤n {suc m} {suc n} f = suc-≤-suc (FinFun→m≤n {!!})

FinFun→Inj : {m n : ℕ} → [ m ↣ n ] → Inj m n
FinFun→Inj {zero} {n} (f , f-inj) = nul _
FinFun→Inj {suc m} {zero} (f , f-inj) = Fin0-absurd (f f0)
FinFun→Inj {suc zero} {suc n} (f , f-inj) = inc (f f0) (nul _)
FinFun→Inj {suc (suc m)} {suc zero} (f , f-inj) = absurd $ fzero≢fsuc (f-inj f0 f1 r)
  where r : f f0 ≡ f f1
        r with f f0 | f f1
        ... | fzero | fzero = refl
FinFun→Inj {suc (suc m)} {suc (suc n)} (f , f-inj) =
  inc (f fzero) (FinFun→Inj (g , g-inj))
  where
    g : ⟦ suc m ⟧ → ⟦ suc n ⟧
    g a = fjoin (f f0) (f (fsuc a)) (≢→≉ᶠ fa'≢f0) 
      where fa'≢f0 : f (fsuc a) ≢ f f0
            fa'≢f0 fa'≡f0 = fsuc≢fzero (f-inj (fsuc a) f0 fa'≡f0 )
    g-inj : is-injective g
    g-inj x y gx≡gy = fsuc-injective (f-inj (fsuc x) (fsuc y) fx'≡fy')
      where
        fx'≉f0 : f (fsuc x) ≉ᶠ f fzero
        fx'≉f0 fx'≈f0 = fsuc≢fzero (f-inj (fsuc x) f0 (≈ᶠ→≡ fx'≈f0))
        fy'≉f0 : f (fsuc y) ≉ᶠ f fzero
        fy'≉f0 fy'≈f0 = fsuc≢fzero (f-inj (fsuc y) f0 (≈ᶠ→≡ fy'≈f0))
        fx'≡fy' : f (fsuc x) ≡ f (fsuc y)
        fx'≡fy' = fjoin-isInjective (f f0) (f (fsuc x)) (f (fsuc y))
                                    fx'≉f0 fy'≉f0 gx≡gy
