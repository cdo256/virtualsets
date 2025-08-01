module VSet.Data.Fin.Splice where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Maybe
open import VSet.Data.Nat.Order
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order

open ℕ.ℕ

private
  variable
    ℓ : Level
    x y : ℕ

fsplice : ∀ {x} → Fin (suc x) → Fin x → Fin (suc x)
fsplice fzero a = fsuc a
fsplice (fsuc b) fzero = fzero
fsplice (fsuc b) (fsuc a) = fsuc (fsplice b a)

-- Alternate definition.
fsplice'-cases : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x) → (Bichotomyᶠ b a)
               → Fin (suc x)
fsplice'-cases _ a (fle _) = fsuc a
fsplice'-cases _ a (fgt _) = finj a

fsplice'-cases-eq
   : ∀ {x} → {b : Fin (suc x)} → {a : Fin x}
   → (u v : Bichotomyᶠ b a)
   → fsplice'-cases b a u ≡ fsplice'-cases b a v
fsplice'-cases-eq (fle u) (fle v) = refl
fsplice'-cases-eq (fle u) (fgt v) = absurd (≤ᶠ→≯ᶠ u v)
fsplice'-cases-eq (fgt u) (fle v) = absurd (≤ᶠ→≯ᶠ v u)
fsplice'-cases-eq (fgt u) (fgt v) = refl

fsplice' : ∀ {x : ℕ} → Fin (suc x) → Fin x → Fin (suc x)
fsplice' b a = fsplice'-cases b a (b ≤?ᶠ a)

fsplice≡fsplice'
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x)
  → fsplice b a ≡ fsplice' b a
fsplice≡fsplice' fzero fzero = refl
fsplice≡fsplice' fzero (fsuc a) = refl
fsplice≡fsplice' (fsuc b) fzero = refl
fsplice≡fsplice' (fsuc b) (fsuc a) with (fsuc b ≤?ᶠ fsuc a)
... | fle b'≤a' = 
  fsuc (fsplice b a)
    ≡⟨ cong fsuc (fsplice≡fsplice' b a) ⟩
  fsuc (fsplice' b a)
    ≡⟨ refl ⟩
  fsuc (fsplice'-cases b a (b ≤?ᶠ a))
    ≡⟨ cong fsuc (fsplice'-cases-eq (b ≤?ᶠ a) (fle (≤-pred b'≤a'))) ⟩
  fsuc (fsplice'-cases b a (fle (≤-pred b'≤a')))
    ≡⟨ refl ⟩
  fsuc (fsuc a)
    ≡⟨ refl ⟩
  fsplice'-cases (fsuc b) (fsuc a) (fle b'≤a') ▯
... | fgt (<fsuc b>a) =
  fsuc (fsplice b a)
    ≡⟨ cong fsuc (fsplice≡fsplice' b a) ⟩
  fsuc (fsplice' b a)
    ≡⟨ refl ⟩
  fsuc (fsplice'-cases b a (b ≤?ᶠ a))
    ≡⟨ cong fsuc (fsplice'-cases-eq (b ≤?ᶠ a) (fgt b>a)) ⟩
  fsuc (fsplice'-cases b a (fgt b>a))
    ≡⟨ refl ⟩
  fsuc (finj a)
    ≡⟨ refl ⟩
  fsplice'-cases (fsuc b) (fsuc a) (fgt (<fsuc b>a)) ▯

antisplice : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
           → Fin (suc x)
antisplice _ fzero = fzero
antisplice fzero (fsuc a) = a
antisplice {suc x} (fsuc b) (fsuc a) =
  fsuc (antisplice b a)

antisplice'-cases : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
           → Bichotomyᶠ a b
           → Fin (suc x)
antisplice'-cases b a (fle a≤b) = fin-restrict-≤ a a≤b
antisplice'-cases b a (fgt a>b) = pred a

antisplice' : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
           → Fin (suc x)
antisplice' b a = antisplice'-cases b a (a ≤?ᶠ b)

-- Remove a from domain of b
funsplice : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc x)) → a ≉ᶠ b
          → Fin x 
funsplice {x = zero} fzero fzero 0≉0 = absurd (0≉0 ≈refl)
funsplice {x = suc zero} _ _ _ = fzero
funsplice {x = suc (suc x)} _ fzero _ = fzero
funsplice {x = suc (suc x)} fzero (fsuc a) _ = a
funsplice {x = suc (suc x)} (fsuc b) (fsuc a) a'≉b' =
  fsuc (funsplice b a λ a≈b → a'≉b' (≈fsuc a≈b))

-- Alternate definition
funsplice' : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x))) → a ≉ᶠ b
           → Fin (suc x)
funsplice' b a a≉b with a ≟ᶠ b
... | flt a<b = fin-restrict a a<b
... | feq a≈b = absurd (a≉b a≈b)
... | fgt b<a = pred a

-- Another alternate definition
funspliceMaybe
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc x))
  → Maybe (Fin x)
funspliceMaybe fzero fzero = nothing
funspliceMaybe {suc x} fzero (fsuc a) = just a
funspliceMaybe {suc x} (fsuc b) fzero = just fzero
funspliceMaybe {suc x} (fsuc b) (fsuc a) =
  map-Maybe fsuc (funspliceMaybe b a)

-- Another alternate definition
funspliceMaybe'
  : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x)))
  → Maybe (Fin (suc x))
funspliceMaybe' b a with a ≟ᶠ b
... | flt a<b = just (fin-restrict a a<b)
... | feq a≡b = nothing
... | fgt b<a = just (pred a)

antisplice≡antisplice'
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
  → antisplice b a ≡ antisplice' b a
antisplice≡antisplice' fzero fzero = refl
antisplice≡antisplice' fzero (fsuc a) = refl
antisplice≡antisplice' (fsuc b) fzero = refl
antisplice≡antisplice' {x = suc x} (fsuc b) (fsuc a) with a ≤?ᶠ b 
... | fle a≤b =
  antisplice (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (antisplice b a)
    ≡⟨ cong fsuc (antisplice≡antisplice' b a) ⟩
  fsuc (antisplice'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ antisplice'-cases b a) (isPropBichotomyᶠ (a ≤?ᶠ b) (fle a≤b)) ⟩
  fsuc (antisplice'-cases b a (fle a≤b))
    ≡⟨ refl ⟩
  fsuc (fin-restrict-≤ a a≤b)
    ≡⟨ refl ⟩
  fsuc (fin-restrict-< a (≤ᶠ→<ᶠ a≤b))
    ≡⟨ cong (fin-restrict-< (fsuc a)) (sym (fsuc≤fsuc→<fsuc a≤b) ) ⟩
  fin-restrict-< (fsuc a) (≤ᶠ→<ᶠ (fsuc≤fsuc a≤b))
    ≡⟨ refl ⟩
  fin-restrict-≤ (fsuc a) (fsuc≤fsuc a≤b)
    ≡⟨ refl ⟩
  antisplice'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fle a≤b))
    ≡⟨ cong (antisplice'-cases (fsuc b) (fsuc a))
            (isPropBichotomyᶠ (≤?ᶠ-suc (fle a≤b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  antisplice'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
... | fgt a>b =
  antisplice (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (antisplice b a)
    ≡⟨ cong fsuc (antisplice≡antisplice' b a) ⟩
  fsuc (antisplice'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ antisplice'-cases b a) (isPropBichotomyᶠ (a ≤?ᶠ b) (fgt a>b)) ⟩
  fsuc (antisplice'-cases b a (fgt a>b))
    ≡⟨ refl ⟩
  fsuc (pred a)
    ≡⟨ fsuc∘pred≡id {y = 1} (≉fsym (<ᶠ→≉ (≤<ᶠ-trans (fzero≤a b) a>b))) ⟩
  a
    ≡⟨ refl ⟩
  antisplice'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fgt a>b))
    ≡⟨ cong (antisplice'-cases (fsuc b) (fsuc a))
            (isPropBichotomyᶠ (≤?ᶠ-suc (fgt a>b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  antisplice'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
