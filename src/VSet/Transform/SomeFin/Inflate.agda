module VSet.Transform.SomeFin.Inflate where

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
open import VSet.Data.Nat.WellFounded 

open import VSet.Transform.SomeFin.Split hiding (sect; retr)

open WFI

0L-R : (A B : Tree ℕ) → Σ∥ A ∥ ≡ 0 →  0L∥ A ＋ B ∥ ≡ suc 0L∥ B ∥
0L-R A B ΣA≡0 =
  0L∥ A ＋ B ∥
    ≡⟨ refl ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
    ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥ )) ΣA≡0 ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) 0
    ≡⟨ refl ⟩
  suc 0L∥ B ∥ ▯

0B<0LA+B : (A B : Tree ℕ) → Σ∥ A ∥ ≡ 0 → 0L∥ B ∥ < 0L∥ A ＋ B ∥
0B<0LA+B A B ΣA≡0 = subst (0L∥ B ∥ <_) (sym (0L-R A B ΣA≡0)) ≤-refl

Σ≢0→Σ≥1 : (A : Tree ℕ) (ΣA≢0 : Σ∥ A ∥ ≢ 0) → Σ ℕ (λ k → k +ℕ 1 ≡ Σ∥ A ∥)
Σ≢0→Σ≥1 A ΣA≢0 = ≢0→≥1 Σ∥ A ∥ ΣA≢0

0A+B≡0A' : (A B : Tree ℕ) → Σ∥ A ∥ ≥ 1 → 0L∥ A ＋ B ∥ ≡ suc 0L∥ A ∥
0A+B≡0A' A B ΣA≥1 =
  0L∥ A ＋ B ∥
    ≡⟨ refl ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
    ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥)) (
        sym (snd (ΣA≥1)) ∙ +-comm (fst (ΣA≥1)) 1) ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) (suc (fst ΣA≥1))
    ≡⟨ refl ⟩
  suc 0L∥ A ∥ ▯

0A<0A+B : (A B : Tree ℕ) → Σ∥ A ∥ ≥ 1 → 0L∥ A ∥ < 0L∥ A ＋ B ∥
0A<0A+B A B ΣA≥1 = subst (0L∥ A ∥ <_) (sym (0A+B≡0A' A B ΣA≥1)) ≤-refl 

≡suc→≥1 : {x y : ℕ} → x ≡ suc y → x ≥ 1
≡suc→≥1 {x} {y} x≡sy = y , +-comm y 1 ∙ sym x≡sy 

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

deflate-rec
  : (A : Tree ℕ) → Acc _≺₀ₗ_ A
  → Tree ℕ
deflate-＋-rec
  : (A B : Tree ℕ) → Singleton Σ∥ A ∥ → Acc _≺₀ₗ_ (A ＋ B)
  → Tree ℕ

deflate-＋-rec A B (zero , ΣA≡0) (acc rs) =
  deflate-rec B (rs B (0B<0LA+B A B ΣA≡0))
deflate-＋-rec A B (suc _ , ΣA≡s) (acc rs) = 
  let
    accA = rs A (0A<0A+B A B (≡suc→≥1 ΣA≡s))
    C = deflate-rec A accA
  in C ＋ B

deflate-rec ⟨ zero ⟩ₜ _ = ⟨ zero ⟩ₜ
deflate-rec ⟨ suc X ⟩ₜ _ = ⟨ suc X ⟩ₜ
deflate-rec (A ＋ B) (acc r) = deflate-＋-rec A B (inspect' Σ∥ A ∥) (acc r)

deflate : Tree ℕ → Tree ℕ
deflate A = deflate-rec A (≺₀ₗ-wellFounded A)

deflateIndependentOfWf : (A : Tree ℕ) → (acc1 acc2 : Acc _≺₀ₗ_ A) →
  deflate-rec A acc1 ≡ deflate-rec A acc2
deflateIndependentOfWf ⟨ zero ⟩ₜ acc1 acc2 = refl
deflateIndependentOfWf ⟨ suc X ⟩ₜ acc1 acc2 = refl
deflateIndependentOfWf (A ＋ B) (acc r1) (acc r2) with inspect' Σ∥ A ∥
... | zero , ΣA≡0 =
  deflate-＋-rec A B (zero , ΣA≡0) (acc r1)
    ≡⟨ refl ⟩
  (deflate-rec B (r1 B 0L-dec))
    ≡⟨ deflateIndependentOfWf B (r1 B 0L-dec)
                                (r2 B 0L-dec) ⟩
  (deflate-rec B (r2 B 0L-dec))
    ≡⟨ refl ⟩
  (deflate-＋-rec A B (zero , ΣA≡0) (acc r2)) ▯
  where 0L-dec : 0L∥ B ∥ < 0L∥ A ＋ B ∥ 
        0L-dec = 0B<0LA+B A B ΣA≡0
... | suc ΣA , ΣA≢0 =
  (deflate-＋-rec A B (suc ΣA , ΣA≢0) (acc r1))
    ≡⟨ refl ⟩
  (deflate-rec A (r1 A 0L-dec)) ＋ B
    ≡⟨ cong (_＋ B) $ deflateIndependentOfWf
      A (r1 A 0L-dec) (r2 A 0L-dec) ⟩
  (deflate-rec A (r2 A 0L-dec)) ＋ B
    ≡⟨ refl ⟩
  (deflate-＋-rec A B (suc ΣA , ΣA≢0) (acc r2)) ▯
  where 0L-dec : 0L∥ A ∥ < 0L∥ A ＋ B ∥
        0L-dec = 0A<0A+B A B (≡suc→≥1 ΣA≢0)

deflate-rec-deflates
  : (A : Tree ℕ) → (acc' : Acc _≺₀ₗ_ A)
  → 0L∥ deflate-rec A acc' ∥ ≡ 0
deflate-＋-rec-deflates
  : (A B : Tree ℕ) → (ΣA : Singleton Σ∥ A ∥) → (acc' : Acc _≺₀ₗ_ (A ＋ B))
  → 0L∥ deflate-＋-rec A B ΣA acc' ∥ ≡ 0
deflate-rec-preserves-Σ
  : (A : Tree ℕ) → (acc' : Acc _≺₀ₗ_ A)
  → Σ∥ A ∥ ≡ Σ∥ deflate-rec A acc' ∥
deflate-＋-rec-preserves-Σ
  : (A B : Tree ℕ) → Singleton Σ∥ A ∥ → (acc' : Acc _≺₀ₗ_ (A ＋ B))
  → Σ∥ A ＋ B ∥ ≡ Σ∥ deflate-＋-rec A B (inspect' Σ∥ A ∥) acc'  ∥


{-
deflateAB≡deflateB : (A B : Tree ℕ) → Σ∥ A ∥ ≡ 0 → fst (deflate (A ＋ B)) ≡ fst (deflate B)
deflateAB≡deflateB A B ΣA≡0 with inspect' Σ∥ A ∥
... | yes ΣA≡0' , ΣA≡0-path =
  fst (deflate (A ＋ B))
    ≡⟨ refl ⟩
  fst (deflate-rec (A ＋ B) (≺₀ₗ-wellFounded (A ＋ B)))
    ≡⟨ refl ⟩
  fst (deflate-＋-rec A B Σ∥ A ∥ (≺₀ₗ-wellFounded (A ＋ B)))
    ≡⟨ cong (λ ○ → fst (deflate-＋-rec A B ○ (≺₀ₗ-wellFounded (A ＋ B))))
            ΣA≡0-path ⟩
  fst (deflate-＋-rec A B (yes ΣA≡0') (≺₀ₗ-wellFounded (A ＋ B)))
    ≡⟨ refl ⟩
  fst (deflate-rec B (accB→accA 0L∥_∥ _<_ B
    (accℕ (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥) 0L∥ B ∥
      (0B<0LA+B A B ΣA≡0'))))
    ≡⟨ deflateIndependentOfWf B ((accB→accA 0L∥_∥ _<_ B
    (accℕ (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥) 0L∥ B ∥
      (0B<0LA+B A B ΣA≡0')))) (≺₀ₗ-wellFounded B) ⟩
  fst (deflate-rec B (≺₀ₗ-wellFounded B))
    ≡⟨ refl ⟩
  fst (deflate B) ▯
... | no ΣA≢0 , _ = absurd (ΣA≢0 ΣA≡0)

deflateAB≡deflateA : (A B : Tree ℕ) → Σ∥ A ∥ ≢ 0 → fst (deflate (A ＋ B)) ≡ fst (deflate A)
deflateAB≡deflateA A B ΣA≢0' with inspect' Σ∥ A ∥
... | yes ΣA≡0 , _ = absurd (ΣA≢0' ΣA≡0)
... | no ΣA≢0 , ΣA≢0-path =
  fst (deflate-＋-rec A B Σ∥ A ∥ (acc r1))
   ≡⟨ cong (λ ○ → fst (deflate-＋-rec A B ○ (acc r1))) ΣA≢0-path ⟩
  fst (deflate-＋-rec A B (no ΣA≢0) (acc r1))
   ≡⟨ refl ⟩
  fst (deflate-rec A (r1 A (0A<0A+B A B ΣA≢0)))
   ≡⟨ deflateIndependentOfWf A (r1 A (0A<0A+B A B ΣA≢0)) (acc r2) ⟩
  fst (deflate-rec A (acc r2)) ▯
  where
    r1 = (λ y y≺'x →
             accB→accA 0L∥_∥ (λ m n → Σ ℕ (λ k → k +ℕ suc m ≡ n)) y
             (accℕ (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥) 0L∥ y ∥ y≺'x))
    r2 = (λ y y≺'x →
        accB→accA 0L∥_∥ (λ m n → Σ ℕ (λ k → k +ℕ suc m ≡ n)) y
        (accℕ 0L∥ A ∥ 0L∥ y ∥ y≺'x))

deflateMap'' : (A : Tree ℕ) → Singleton Σ∥ A ∥
            → ⟦ A ⟧ₛ → ⟦ fst (deflate A) ⟧ₛ
deflateMap' : (A B : Tree ℕ) → (Σ∥ A ＋ B ∥ ≢ 0) → Singleton Σ∥ A ∥ 
            → ⟦ A ＋ B ⟧ₛ → ⟦ fst (deflate (A ＋ B)) ⟧ₛ

deflateMap'' C (yes ΣC≡0) a = absurd (Σ≡0→Empty C ΣC≡0 a)
deflateMap'' ⟨ suc X ⟩ₜ (no ΣC≢0) a = a
deflateMap'' (A ＋ B) (no ΣC≢0) a =
  deflateMap' A B (ΣC≢0) Σ∥ A ∥ a

deflateMap' A B ΣAB≢0 (yes ΣA≡0) (inl a) = absurd (Σ≡0→Empty A ΣA≡0 a)
deflateMap' A B ΣAB≢0 (yes ΣA≡0) (inr a) =
  subst ⟦_⟧ₛ (sym $ deflateAB≡deflateB A B ΣA≡0) (deflateMap'' B Σ∥ B ∥ a)
deflateMap' A B ΣAB≢0 (no ΣA≢0) (inl a) =
  subst (⟦_⟧ₛ) {!eq'!} (inl (deflateMap'' A (no ΣA≢0) a))
  -- (subst ⟦ deflateMap' A B ΣAB≢0 (no ΣA≢0) ⟧ₛ {!!} (inl (deflateMap'' A (no ΣA≢0) a)))
  where
    eq' : fst (deflate (A + B)) ≡ fst (deflate  B )
deflateMap' A B ΣAB≢0 (no ΣA≢0) (inr a) = {!!}

deflateMap : (A : Tree ℕ) → ⟦ A ⟧ₛ → ⟦ fst (deflate A) ⟧ₛ
deflateMap A a with Σ∥ A ∥
deflateMap A a | yes z = absurd (Σ≡0→Empty A z a)
deflateMap ⟨ suc X ⟩ₜ a | no ¬z = a
deflateMap (A ＋ B) a | no ¬z with inspect' Σ∥ A ∥
deflateMap (A ＋ B) (inl a) | no ¬z | yes ΣA≡0 , ΣA≡0-path = absurd (Σ≡0→Empty A ΣA≡0 a)
deflateMap (A ＋ B) (inr a) | no ¬z | yes ΣA≡0 , ΣA≡0-path =
  subst ⟦_⟧ₛ (sym (deflateAB≡deflateB A B ΣA≡0)) (deflateMap B a)
deflateMap (A ＋ B) a | no ¬z₁ | no ¬z , _ = {!!}



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
-- -}
-- -}
-- -}
-- -}
