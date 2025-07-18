module VSet.Transform.Split where

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Data.Nat renaming (_+_ to _+ℕ_)
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Properties

open Iso

⊎→+ : ∀ {X Y : SomeFin} → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ X + Y ⟧
⊎→+ {X} {Y} (inl a) = finject Y a
⊎→+ {X} {Y} (inr a) = fshift X a

inc : ∀ {X Y : SomeFin} → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ suc X ⟧ ⊎ ⟦ Y ⟧
inc (inl a) = inl (fsuc a)
inc (inr a) = inr a

+→⊎ : ∀ {X Y : SomeFin} → ⟦ X + Y ⟧ → ⟦ X ⟧ ⊎ ⟦ Y ⟧
+→⊎ {zero} {Y} a = inr a
+→⊎ {suc X} {Y} fzero = inl fzero
+→⊎ {suc X} {Y} (fsuc a) = inc (+→⊎ {X} {Y} a)

sect : ∀ {X Y : SomeFin} → section {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} ⊎→+ +→⊎
sect {zero} {Y} a = refl
sect {suc X} {zero} fzero = refl
sect {suc X} {suc Y} fzero = refl
sect {suc X} {zero} (fsuc a) =
  ⊎→+ (+→⊎ (fsuc a)) ≡⟨ refl ⟩
  fsuc a ∎
sect {suc X} {suc Y} (fsuc a) with +→⊎ a
... | inl b = 
  ⊎→+ (+→⊎ (fsuc a)) ≡⟨ refl ⟩
  ⊎→+ (inc (+→⊎ a)) ≡⟨ refl ⟩
  ⊎→+ (inc (inl b)) ≡⟨ refl ⟩
  ⊎→+ (inl (fsuc b)) ≡⟨ refl ⟩
  fsuc a ∎
... | inr b =
  ⊎→+ (+→⊎ (fsuc a)) ≡⟨ refl ⟩
  ⊎→+ (inc (+→⊎ a)) ≡⟨ refl ⟩
  fsuc a ∎

retr : ∀ {X Y : SomeFin} → retract {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} ⊎→+ +→⊎
retr {zero} {Y} (inr a) = refl
retr {suc X} {Y} (inl fzero) =
  +→⊎ (⊎→+ (inl fzero)) ≡⟨ refl ⟩
  +→⊎ fzero ≡⟨ refl ⟩
  inl fzero ∎
retr {suc X} {zero} (inl (fsuc a)) =
  +→⊎ (⊎→+ (inl (fsuc a))) ≡⟨ refl ⟩
  +→⊎ (finject 0 (fsuc a)) ≡⟨ refl ⟩
  +→⊎ {suc X} {zero} (fsuc (finject 0 a)) ≡⟨ refl ⟩
  inc (+→⊎ {X} {zero} (finject 0 a)) ≡⟨ refl ⟩
  inc (+→⊎ {X} {zero} (⊎→+ {X} {zero} (inl a))) ≡⟨ cong inc (retr (inl a)) ⟩
  inl (fsuc a) ∎
retr {suc X} {suc Y} (inl (fsuc a)) =
  +→⊎ (⊎→+ (inl (fsuc a))) ≡⟨ refl ⟩
  +→⊎ (finject {suc X} (suc Y) (fsuc a)) ≡⟨ refl ⟩
  +→⊎ (fsuc (finject {X} (suc Y) a)) ≡⟨ refl ⟩
  +→⊎ {suc X} {suc Y} (fsuc (finject {X} (suc Y) a)) ≡⟨ refl ⟩
  inc (+→⊎ (finject {X} (suc Y) a)) ≡⟨ refl ⟩
  inc (+→⊎ (⊎→+ (inl a))) ≡⟨ cong inc (retr (inl a)) ⟩
  inc (inl a) ≡⟨ refl ⟩
  inl (fsuc a) ∎
retr {suc X} {Y} (inr a) =
  +→⊎ (⊎→+ (inr a)) ≡⟨ refl ⟩
  +→⊎ (fshift (suc X) a) ≡⟨ refl ⟩
  +→⊎ (fsuc (fshift X a)) ≡⟨ refl ⟩
  inc (+→⊎ (fshift X a)) ≡⟨ refl ⟩
  inc (+→⊎ (⊎→+ (inr a))) ≡⟨ cong inc (retr (inr a)) ⟩
  inc (inr a) ≡⟨ refl ⟩
  inr a ∎

⊎↔+ : ∀ {X Y : SomeFin} → Iso (⟦ X ⟧ ⊎ ⟦ Y ⟧) ⟦ X +ℕ Y ⟧
⊎↔+ {X} {Y} = iso ⊎→+ +→⊎ sect retr
