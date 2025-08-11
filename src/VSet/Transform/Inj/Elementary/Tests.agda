module VSet.Transform.Inj.Elementary.Tests where

open import VSet.Prelude
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inj.Elementary.Base

private
  variable
    l l' m m' n n' : ℕ


g : Inj 4 6 -- (3 2 4 0)
g = (inc f3 $ inc f2 $ inc f2 $ inc f0 $ nul 2)

_ : bubble f3 g ≡ (inc f4 $ inc f2 $ inc f3 $ inc f0 $ nul 3)
_ = refl

_ : bubble f0 g ≡ (inc f4 $ inc f3 $ inc f3 $ inc f1 $ nul 3)
_ = refl

_ : excise f0 g ≡ (inc f2 $ inc f3 $ inc f0 $ nul 3)
_ =
  excise f0 (inc f3 $ inc f2 $ inc f2 $ inc f0 $ nul 2) ≡⟨ refl ⟩
  bubble f3 (inc f2 $ inc f2 $ inc f0 $ nul 2) ≡⟨ refl ⟩
  inc (fsplice f3 f2) (bubble f2 (inc f2 $ inc f0 $ nul 2)) ≡⟨ refl ⟩
  inc f2 (bubble f2 (inc f2 $ inc f0 $ nul 2)) ≡⟨ refl ⟩
  inc f2 (inc f3 (bubble (fcross f2 f2) (inc f0 $ nul 2))) ≡⟨ refl ⟩
  inc f2 (inc f3 (bubble f2 (inc f0 $ nul 2))) ≡⟨ refl ⟩
  inc f2 (inc f3 (inc f0 (bubble f1 $ nul 2))) ≡⟨ refl ⟩
  inc f2 (inc f3 (inc f0 (nul 3))) ≡⟨ refl ⟩
  (inc f2 $ inc f3 $ inc f0 $ nul 3) ▯

_ : apply g f1 ≡ f2
_ = refl

3≉2 : {x : ℕ} → f3 {3 + x} ≉ᶠ f2 {3 + x}
3≉2 (≈fsuc (≈fsuc ()))

-- (2 3 0)
_ : remove f1 g ≡ (inc f2 $ inc f2 $ inc f0 $ nul 2)
_ = remove f1 g ≡⟨ refl ⟩
    inc (fjoin (fsplice f3 f2) f3
               (fsplice≉b (fsplice f3 f2) f2))
        (remove f0 (inc f2 $ inc f2 $ inc f0 $ nul 2)) ≡⟨ refl ⟩
    inc (fjoin f2 f3 (fsplice≉b (fsplice f3 f2) f2))
        (remove f0 (inc f2 $ inc f2 $ inc f0 $ nul 2)) ≡⟨ refl ⟩
    inc f2 (remove f0 (inc f2 $ inc f2 $ inc f0 $ nul 2)) ≡⟨ refl ⟩
    (inc f2 $ inc f2 $ inc f0 $ nul 2)  ▯

-- (3 4 0)
_ : excise f1 g ≡ (inc f3 $ inc f3 $ inc f0 $ nul 3)
_ =
  excise f1 g ≡⟨ refl ⟩
  bubble (apply g f1) (remove f1 g) ≡⟨ refl ⟩
  bubble f2 (remove f1 g) ≡⟨ refl ⟩
  bubble f2 (inc f2 $ inc f2 $ inc f0 $ nul 2) ≡⟨ refl ⟩
  (inc f3 $ inc f3 $ inc f0 $ nul 3) ▯
