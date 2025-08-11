module VSet.Transform.FinFun.Flatten where

open import VSet.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order

open import VSet.Data.Nat hiding (¬-<-zero)
open import VSet.Data.Fin.Base
open import VSet.Data.SumTree.Base
open import VSet.Data.SumTree.Metrics

open import VSet.Data.Fin.SumSplit hiding (sect; retr)

flatten : (A : Tree ℕ) → ⟦ A ⟧ₛ → ⟦ Σ∥ A ∥ ⟧
flatten ⟨ X ⟩ₜ a = a
flatten (A ＋ B) (inl x) = ⊎→+ Σ∥ A ∥ Σ∥ B ∥ (inl (flatten A x))
flatten (A ＋ B) (inr y) = ⊎→+ Σ∥ A ∥ Σ∥ B ∥ (inr (flatten B y))

unflatten : (A : Tree ℕ) → ⟦ Σ∥ A ∥ ⟧ → ⟦ A ⟧ₛ
unflatten ⟨ X ⟩ₜ a = a
unflatten (A ＋ B) a with +→⊎ Σ∥ A ∥ Σ∥ B ∥ a
... | inl x = inl (unflatten A x)
... | inr y = inr (unflatten B y)

drop-0-base : (A : Tree ℕ) → Tree ℕ
drop-0-base ⟨ X ⟩ₜ = ⟨ X ⟩ₜ
drop-0-base (A ＋ B) with Σ∥ A ∥ | Σ∥ B ∥
... | zero | bn = drop-0-base B
... | suc an | zero = drop-0-base A
... | suc an | suc bn = drop-0-base A ＋ drop-0-base B

{-
drop-0-no-0 : (A : Tree ℕ) → (an : ℕ) → Σ∥ A ∥ ≡ suc an → no-0 (drop-0-base A)
drop-0-drops-0 : (A : Tree ℕ) → ∥ A ∥ₜ ≥ 1 → no-0 (drop-0-base A)

drop-0-no-0 A an a≡ = drop-0-drops-0 A (subst (_≥ 1) (sym a≡) (suc≥1 an))

drop-0-drops-0 ⟨ X ⟩ₜ ge = ge
drop-0-drops-0 (A ＋ B) ge
  with ∥ A ∥ₜ | inspect ∥_∥ₜ A | ∥ B ∥ₜ | inspect ∥_∥ₜ B
... | zero | [ a≡ ]ᵢ | zero | [ b≡ ]ᵢ =
  absurd {A = λ _ → no-0 (drop-0-base (⟨ zero ⟩ₜ ＋ B))} (¬-<-zero ge) 
... | zero | [ a≡ ]ᵢ | suc bn | [ b≡ ]ᵢ = drop-0-drops-0 B 
  (subst (_≥ 1) (sym b≡) (suc≥1 bn)) 
... | suc an | [ a≡ ]ᵢ | zero | [ b≡ ]ᵢ = drop-0-drops-0 A 
  (subst (_≥ 1) (sym a≡) (suc≥1 an)) 
... | suc an | [ a≡ ]ᵢ | suc bn | [ b≡ ]ᵢ = noA , noB
  where
    noA : no-0 (drop-0-base A)
    noA = drop-0-drops-0 A (subst (_≥ 1) (sym a≡) (suc≥1 an))
    noB : no-0 (drop-0-base B)
    noB = drop-0-drops-0 B (subst (_≥ 1) (sym b≡) (suc≥1 bn))

drop-0-preserves-size : (A : Tree ℕ) → ∥ drop-0-base A ∥ₜ ≡ ∥ A ∥ₜ
drop-0-preserves-size ⟨ X ⟩ₜ = refl
drop-0-preserves-size (A ＋ B)
  with ∥ A ∥ₜ | inspect ∥_∥ₜ A | ∥ B ∥ₜ | inspect ∥_∥ₜ B
... | zero | [ a≡ ]ᵢ | bn | [ b≡ ]ᵢ =
  drop-0-preserves-size B ∙ b≡
... | suc an | [ a≡ ]ᵢ | zero | [ b≡ ]ᵢ =
  drop-0-preserves-size A ∙ a≡ ∙ cong suc (sym (+-zero an))
... | suc an | [ a≡ ]ᵢ | suc bn | [ b≡ ]ᵢ = 
  ∥ drop-0-base A ∥ₜ + ∥ drop-0-base B ∥ₜ
    ≡⟨ cong₂ _+_ (drop-0-preserves-size A) (drop-0-preserves-size B) ⟩
  ∥ A ∥ₜ + ∥ B ∥ₜ
    ≡⟨ cong₂ _+_ a≡ b≡ ⟩
  suc an + suc bn ▯

drop-0 : Tree+ → Tree+∖0
drop-0 (A , A≥1) with ∥ A ∥ₜ | inspect ∥_∥ₜ A
... | zero | [ A≡0 ]ᵢ = absurd {A = λ _ → Tree+∖0} (0≱y+1 zero A≥1)
... | suc n | [ A≡n' ]ᵢ = drop-0-base A , (drop-0-no-0 A n A≡n' , dropA≥1)
  where
    dropA≥1 : ∥ drop-0-base A ∥ₜ ≥ 1
    dropA≥1 = subst (_≥ 1) (sym A≡n' ∙ sym (drop-0-preserves-size A)) A≥1

Tree+∖0→Tree+ : (A : Tree+) → ⟦ fst (drop-0 A) ⟧ₛ → ⟦ fst A ⟧ₛ
Tree+∖0→Tree+ (⟨ zero ⟩ₜ , 0≥1) _ =
  absurd {A = λ _ → ⟦ ⟨ zero ⟩ₜ ⟧ₛ} (0≱1 0≥1)
Tree+∖0→Tree+ (⟨ suc X ⟩ₜ , ge) a = a
Tree+∖0→Tree+ ((A ＋ B) , ge) a =
  helper ∥ A ∥ₜ (inspect ∥_∥ₜ A) (∥ B ∥ₜ) (inspect ∥_∥ₜ B)
  where
    helper : (an : ℕ) → Reveal ∥_∥ₜ · A is an → (bn : ℕ) → Reveal ∥_∥ₜ · B is bn →  ⟦ A ＋ B ⟧ₛ  
    helper zero [ A≡an ]ᵢ bn [ B≡bn ]ᵢ = {!!}
    helper (suc an) [ A≡an ]ᵢ bn [ B≡bn ]ᵢ = {!!}

--   with w -- | ∥ A ∥ₜ | inspect ∥_∥ₜ A | ∥ B ∥ₜ | inspect ∥_∥ₜ B
-- ... | w' = {!!} --| _ | _ | _ = ?

-- ... | zero | [ a≡ ]ᵢ | bn | [ b≡ ]ᵢ =
--   ?
-- ... | suc an | [ a≡ ]ᵢ | zero | [ b≡ ]ᵢ =
--   ?
-- ... | suc an | [ a≡ ]ᵢ | suc bn | [ b≡ ]ᵢ = 
--   ?


{-
drop-1L : (A : Tree ℕ) → no-0 A → Tree ℕ
drop-1L ⟨ zero ⟩ₜ no0 = absurd {A = λ _ → Tree ℕ} (¬-<-zero no0)
drop-1L ⟨ suc X ⟩ₜ no0 = ⟨ X ⟩ₜ
drop-1L (A ＋ B) (A-no0 , _) = drop-1L A A-no0 ＋ B

sect : (A : Tree ℕ) → section (flatten A) (unflatten A)
sect ⟨ x ⟩ₜ b = refl
sect (A ＋ B) b = {!!}
  -- flatten A (unflatten A b) ≡⟨ {!!} ⟩
  -- flatten A (unflatten A b) ≡⟨ {!!} ⟩
  -- b ▯

-- -}
-- -}
-- -}
