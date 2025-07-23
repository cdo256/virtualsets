module VSet.Transform.Inflate where

open import VSet.Prelude

open import Cubical.Data.Nat.Order

open import VSet.Data.Nat hiding (_+_; ¬-<-zero)
open import VSet.Data.Fin
open import VSet.Data.SomeFin.Base
open import VSet.Data.SumTree.Base
open import VSet.Data.SumTree.Metrics
open import Cubical.Data.Nat.Order
open import Cubical.Induction.WellFounded
open import VSet.Relation.WellFounded.Base 
open import VSet.Relation.WellFounded.Lex 
open import Cubical.Relation.Binary.Base 

open import VSet.Transform.Split hiding (sect; retr)

open WFI

deflate' : (A : Tree ℕ) → Acc _≺₀ₗ_ A → DeflatedTree
deflate' ⟨ zero ⟩ₜ _ = ⟨ zero ⟩ₜ , refl
deflate' ⟨ suc X ⟩ₜ _ = ⟨ suc X ⟩ₜ , refl
deflate' (A ＋ B) (acc rs) with inspect' Σ∥ A ∥
... | zero , ΣA≡0 = deflate' B (rs B 0B<0LA+B)
  where
    rw : 0L∥ A ＋ B ∥ ≡ suc 0L∥ B ∥
    rw =
      0L∥ A ＋ B ∥
        ≡⟨ refl ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
        ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥ )) ΣA≡0 ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) 0
        ≡⟨ refl ⟩
      suc 0L∥ B ∥ ▯
    0B<0LA+B : 0L∥ B ∥ < 0L∥ A ＋ B ∥
    0B<0LA+B = subst (0L∥ B ∥ <_) (sym rw) ≤-refl
... | suc n , ΣA≡s = deflate' A (rs A 0A<0A+B)
  where
    0A+B≡0A' : 0L∥ A ＋ B ∥ ≡ suc 0L∥ A ∥
    0A+B≡0A' =
      0L∥ A ＋ B ∥
        ≡⟨ refl ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
        ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥)) ΣA≡s ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) (suc n)
        ≡⟨ refl ⟩
      suc 0L∥ A ∥ ▯
    0A<0A+B : 0L∥ A ∥ < 0L∥ A ＋ B ∥
    0A<0A+B = subst (0L∥ A ∥ <_) (sym 0A+B≡0A') ≤-refl 

deflate : (A : TreeΣ+) → Acc _≺₀ₗ_ (fst A) → DeflatedTree
deflate (⟨ zero ⟩ₜ , Σ+) _ = absurd {A = λ _ → DeflatedTree} (0≱suc 0 Σ+)
deflate (⟨ suc X ⟩ₜ , Σ+) _ = ⟨ suc X ⟩ₜ , refl
deflate (A ＋ B , Σ+) (acc rs) with inspect' Σ∥ A ∥
... | zero , ΣA≡0 = deflate (B , subst (λ ○ → ○ + Σ∥ B ∥ ≥ 1) ΣA≡0 Σ+)
                             (rs B 0B<0LA+B)
  where
    rw : 0L∥ A ＋ B ∥ ≡ suc 0L∥ B ∥
    rw =
      0L∥ A ＋ B ∥
        ≡⟨ refl ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
        ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥ )) ΣA≡0 ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) 0
        ≡⟨ refl ⟩
      suc 0L∥ B ∥ ▯
    0B<0LA+B : 0L∥ B ∥ < 0L∥ A ＋ B ∥
    0B<0LA+B = subst (0L∥ B ∥ <_) (sym rw) ≤-refl
... | suc n , ΣA≡s = deflate (A , subst (_≥ 1) (sym ΣA≡s) (suc≥1 n))
                              (rs A 0A<0A+B)
  where
    0A+B≡0A' : 0L∥ A ＋ B ∥ ≡ suc 0L∥ A ∥
    0A+B≡0A' =
      0L∥ A ＋ B ∥
        ≡⟨ refl ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
        ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥)) ΣA≡s ⟩
      forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) (suc n)
        ≡⟨ refl ⟩
      suc 0L∥ A ∥ ▯
    0A<0A+B : 0L∥ A ∥ < 0L∥ A ＋ B ∥
    0A<0A+B = subst (0L∥ A ∥ <_) (sym 0A+B≡0A') ≤-refl 

-- deflate : (A : Tree ℕ) → DeflatedTree
-- deflate A with ≡0? Σ∥ A ∥
-- ... | yes z = ⟨ 0 ⟩ₜ , refl
-- ... | no ¬z = deflate' (A , ≢0→≥1 Σ∥ A ∥ ¬z) (≺₀ₗ-wellFounded A)

Σ≡0→Empty : (A : Tree ℕ) → (Σ∥ A ∥ ≡ 0) → ¬ ⟦ A ⟧ₛ
Σ≡0→Empty ⟨ X ⟩ₜ Σ≡0 a = equivFun Fin0≃⊥ (transport {A = ⟦ ⟨ X ⟩ₜ ⟧ₛ} eq' a)
  where
    eq' : ⟦ ⟨ X ⟩ₜ ⟧ₛ ≡ Fin 0
    eq' =
      ⟦ ⟨ X ⟩ₜ ⟧ₛ
        ≡⟨ refl ⟩
      [_]ₛ (map ⟦_⟧ ⟨ X ⟩ₜ)
        ≡⟨ refl ⟩
      [_]ₛ (fold (λ Y → ⟨ ⟦ Y ⟧ ⟩ₜ) _＋_ ⟨ X ⟩ₜ)
        ≡⟨ refl ⟩
      [_]ₛ ⟨ ⟦ X ⟧ ⟩ₜ
        ≡⟨ refl ⟩
      ⟦ X ⟧
        ≡⟨ refl ⟩
      Fin X
        ≡⟨ cong Fin Σ≡0 ⟩
      Fin 0 ▯
Σ≡0→Empty (A ＋ B) Σ≡0 (inl a) = Σ≡0→Empty A (≤0→≡0 ΣA≤0) a
  where ΣA≤0 : Σ∥ A ∥ ≤ 0
        ΣA≤0 = Σ∥ B ∥ , +-comm Σ∥ B ∥ Σ∥ A ∥ ∙ Σ≡0
Σ≡0→Empty (A ＋ B) Σ≡0 (inr a) = Σ≡0→Empty B (≤0→≡0 ΣB≤0) a
  where ΣB≤0 : Σ∥ B ∥ ≤ 0
        ΣB≤0 = Σ∥ A ∥ , Σ≡0

{-
deflateMap : (A : Tree ℕ) → ⟦ A ⟧ₛ → ⟦ fst (deflate A) ⟧ₛ
deflateMap A a with ≡0? Σ∥ A ∥
deflateMap A a | yes z = absurd (Σ≡0→Empty A z a)
deflateMap ⟨ suc X ⟩ₜ a | no ¬z = a
deflateMap (A ＋ B) a | no ¬z with ≡0? Σ∥ A ∥
deflateMap (A ＋ B) (inl a) | no ¬z | yes z' = absurd (Σ≡0→Empty A z' a)
deflateMap (A ＋ B) (inr a) | no ¬z | yes z' =
  deflateMap {!B!} a
  where
    ΣAB≡B : Σ∥ A ＋ B ∥ ≡ Σ∥ B ∥
    ΣAB≡B =
      Σ∥ A ＋ B ∥ ≡⟨ refl ⟩
      Σ∥ A ∥ + Σ∥ B ∥ ≡⟨ cong (_+ Σ∥ B ∥) z' ⟩
      0 + Σ∥ B ∥ ≡⟨ refl ⟩
      Σ∥ B ∥ ▯
    deflateAB≡deflateB : deflate (A ＋ B) ≡ deflate B
    deflateAB≡deflateB =
      deflate (A ＋ B)
        ≡⟨ {!refl!} ⟩
      deflate' ((A ＋ B) , ≢0→≥1 Σ∥ A ＋ B ∥ ¬z) (≺₀ₗ-wellFounded (A ＋ B))
        ≡⟨ {!!} ⟩
      {!!} ▯
... | no ¬z = {!!}

{-
step : (A : TreeΣ+) → Tree ℕ
step (⟨ zero ⟩ₜ , Σ+) = absurd (0≱suc 0 Σ+)
step (⟨ suc X ⟩ₜ , Σ+) = ⟨ X ⟩ₜ
step (A ＋ B , Σ+) with Σ∥ A ∥ | inspect Σ∥_∥ A
... | zero | _ = B
... | suc w | [ eq' ]ᵢ = (step (A , {!suc≥1 !})) ＋ B

pop : ∀ (A : TreeΣ+) → Tree ℕ
pop A = let w = WFRec _≺ₘ_ P (fst A) in A .fst
  where
    P : Tree ℕ → Type
    P D = Σ∥ D ∥ ≡ Σ∥ fst A ∥
  
-- pop : ∀ (A : TreeΣ+) → Tree ℕ
-- pop A = induction ≺ₘ-wellFounded {!!} {!!}
--   where
--     P : Tree ℕ → Type
--     P D = Σ∥ D ∥ ≡ Σ∥ fst A ∥
--     e : (B : Tree ℕ) → ((C : Tree ℕ) → C ≺ₘ B → P C) → P B
--     e B C<B→PC = {!!}

{-

drop-0-base : (A : Tree ℕ) → Tree ℕ
drop-0-base ⟨ X ⟩ₜ = ⟨ X ⟩ₜ
drop-0-base (A ＋ B) with Σ∥ A ∥ | Σ∥ B ∥
... | zero | bn = drop-0-base B
... | suc an | zero = drop-0-base A
... | suc an | suc bn = drop-0-base A ＋ drop-0-base B

drop-0-no-0 : (A : Tree ℕ) → (an : ℕ) → ∥ A ∥ₜ ≡ suc an → no-0 (drop-0-base A)
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
-- -}
