module VSet.Transform.Compose.Properties where

open import VSet.Prelude
open import Cubical.Data.Prod.Base hiding (map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import Cubical.Data.List.Base hiding ([_])
open import VSet.Data.Inj.Base
open import VSet.Transform.Compose.Base
open import VSet.Transform.Elementary.Base

applyId : ∀ {m : ℕ} (a : Fin m) → apply (idInj m) a ≡ a
applyId fzero = refl
applyId (fsuc a) = cong fsuc (applyId a)

removeId : ∀ {m : ℕ} (a : Fin (suc m)) → remove a (idInj (suc m)) ≡ idInj m
removeId fzero = refl
removeId {m = m} (fsuc a) =
  remove (fsuc a) (idInj (suc m))
    ≡⟨ refl ⟩
  remove (fsuc a) (inc fzero (idInj m))
    ≡⟨ {!!} ⟩
  idInj m ▯

∘ʲ-idL : ∀ {m n : ℕ} (f : Inj m n) → idInj n ∘ʲ f ≡ f
∘ʲ-idL (nul _) = refl
∘ʲ-idL {n = suc n} (inc b f) =
 idInj (suc n) ∘ʲ inc b f
   ≡⟨ refl ⟩
 inc (apply (idInj (suc n)) b) (remove b (idInj (suc n)) ∘ʲ f)
   ≡⟨ cong₂ inc (applyId b) {!!} ⟩
 inc b (remove b (idInj (suc n)) ∘ʲ f)
   ≡⟨ cong₂ inc {!∘ʲ-idL!} {!!} ⟩
 inc b f ▯

∘ʲ-idR : ∀ {m n : ℕ} (f : Inj m n) → f ∘ʲ idInj m ≡ f
∘ʲ-idR (nul _) = refl
∘ʲ-idR {m = suc m} (inc b f) =
  inc b f ∘ʲ idInj (suc m)
    ≡⟨ refl ⟩
  inc b f ∘ʲ inc fzero (idInj m)
    ≡⟨ cong (inc b) (∘ʲ-idR f) ⟩
  inc b f ▯

∘ʲ-assoc : ∀ {k l m n : ℕ} → (h : Inj m n) → (g : Inj l m) → (f : Inj k l)
         → h ∘ʲ (g ∘ʲ f) ≡ (h ∘ʲ g) ∘ʲ f
∘ʲ-assoc (nul _) (nul _) (nul _) = refl
∘ʲ-assoc (inc _ _) _ (nul _) = refl
∘ʲ-assoc (inc c h) (inc b g) (inc a f) =
 {!!} ≡⟨ {!!} ⟩
 {!!} ▯
