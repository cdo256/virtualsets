module VSet.Transform.FinFun.Tensor where

open import VSet.Prelude
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import Cubical.Data.Nat.Properties

open import VSet.Data.Nat using (ℕ; zero; suc; _+_)
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.Sum.Properties
open import VSet.Data.FinFun.Injection
open import VSet.Data.FinFun.Equality
open import VSet.Data.Fin.SumSplit
open import VSet.Transform.FinFun.Pred
open import VSet.Transform.FinFun.Compose


tensor : ∀ {k l m n : ℕ} → [ k ↣ l ] → [ m ↣ n ] → [ k + m ↣ l + n ]
tensor {k} {l} {m} {n} f g = ↔to↣ (⊎↔+ l n) ↣∘↣ ↣-map-⊎ f g ↣∘↣ ↔to↣ (flip-↔ (⊎↔+ k m))

𝟘 : [ 0 ↣ 0 ]
𝟘 = ↣-id ⟦ 0 ⟧

infixl 30 _⊕_

_⊕_ : ∀ {k l m n : ℕ} → [ k ↣ l ] → [ m ↣ n ] → [ k + m ↣ l + n ]
f ⊕ g = tensor f g
 
𝟙⊕𝟙≡𝟙 : {m n : ℕ} → 𝟙 {m} ⊕ 𝟙 {n} ≈ 𝟙 {m + n}
𝟙⊕𝟙≡𝟙 {m} {n} = record { p = refl ; q = refl ; path = r }
  where
    r : (⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n) ≡ id
    r =
      ⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m n ∘ ○ ∘ +→⊎ m n) ⊎-map-id≡id ⟩
      ⊎→+ m n ∘ +→⊎ m n
        ≡⟨ funExt (sect m n) ⟩
      id ▯

ladd : ∀ {l m : ℕ} → (A : ℕ) → [ l ↣ m ] → [ A + l ↣ A + m ]
ladd {l} {m} A f = (↣-id ⟦ A ⟧) ⊕ f

radd : ∀ {l m : ℕ} → (A : ℕ) → [ l ↣ m ] → [ l + A ↣ m + A ]
radd {l} {m} A f = f ⊕ (↣-id ⟦ A ⟧)

⊕-preserves-∘
  : ∀ {m m' m'' n n' n''}
  → (f : [ m ↣ m' ]) (f' : [ m' ↣ m'' ]) (g : [ n ↣ n' ]) (g' : [ n' ↣ n'' ])
  → (f' ∘ʲ f) ⊕ (g' ∘ʲ g) ≈ (f' ⊕ g') ∘ʲ (f ⊕ g)
⊕-preserves-∘ {m} {m'} {m''} {n} {n'} {n''} f f' g g' =
  record { p = refl ; q = refl ; path = e }
  where
    e : ⊎→+ m'' n'' ∘ ⊎-map (fst f' ∘ fst f) (fst g' ∘ fst g) ∘ +→⊎ m n
      ≡ (⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ +→⊎ m' n')
      ∘  (⊎→+ m' n' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n)
    e =
      ⊎→+ m'' n'' ∘ ⊎-map (fst f' ∘ fst f) (fst g' ∘ fst g) ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m'' n'' ∘ ○ ∘ +→⊎ m n)
                (sym (⊎-map-∘ (fst f) (fst f') (fst g) (fst g'))) ⟩
      ⊎→+ m'' n'' ∘ (⊎-map (fst f') (fst g') ∘ ⊎-map (fst f) (fst g)) ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m'' n'' ∘ (⊎-map (fst f') (fst g') ∘ ○ ∘ ⊎-map (fst f) (fst g)) ∘ +→⊎ m n)
                (sym (funExt (retr m' n'))) ⟩
      ⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ (+→⊎ m' n' ∘
        ⊎→+ m' n') ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n
        ≡⟨ refl ⟩
      (⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ +→⊎ m' n') ∘
        ⊎→+ m' n' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n ▯
