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
fsplice'-cases : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x) → (Dichotomyᶠ b a)
               → Fin (suc x)
fsplice'-cases _ a (fle _) = fsuc a
fsplice'-cases _ a (fgt _) = finj a

fsplice'-cases-eq
   : ∀ {x} → {b : Fin (suc x)} → {a : Fin x}
   → (u v : Dichotomyᶠ b a)
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

fcross : ∀ {x : ℕ} → (b : Fin x) → (a : Fin (suc x)) → Fin x
fcross fzero fzero = fzero
fcross (fsuc b) fzero = fzero
fcross fzero (fsuc a) = a
fcross (fsuc b) (fsuc a) = fsuc (fcross b a)

fcross₂ : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
            → Fin (suc x)
fcross₂ _ fzero = fzero
fcross₂ fzero (fsuc a) = a
fcross₂ {suc x} (fsuc b) (fsuc a) =
  fsuc (fcross₂ b a)

fcross'-cases
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
  → Dichotomyᶠ a b
  → Fin (suc x)
fcross'-cases b a (fle a≤b) = fin-restrict-≤ a a≤b
fcross'-cases b a (fgt a>b) = pred a

fcross' : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
        → Fin (suc x)
fcross' b a = fcross'-cases b a (a ≤?ᶠ b)

fjoin-cases : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
                → Trichotomyᶠ a b → Fin x
fjoin-cases b a a≉b (flt a<b) = fin-restrict-< a a<b
fjoin-cases b a a≉b (feq a≈b) = absurd (a≉b a≈b)
fjoin-cases b (fsuc a) a≉b (fgt b<a) = a

fjoin : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
           → Fin x
fjoin b a a≉b = fjoin-cases b a a≉b (a ≟ᶠ b)

-- Another alternate definition
fjoinMaybe
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc x))
  → Maybe (Fin x)
fjoinMaybe fzero fzero = nothing
fjoinMaybe {suc x} fzero (fsuc a) = just a
fjoinMaybe {suc x} (fsuc b) fzero = just fzero
fjoinMaybe {suc x} (fsuc b) (fsuc a) =
  map-Maybe fsuc (fjoinMaybe b a)

-- Another alternate definition
fjoinMaybe'
  : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x)))
  → Maybe (Fin (suc x))
fjoinMaybe' b a with a ≟ᶠ b
... | flt a<b = just (fin-restrict-< a a<b)
... | feq a≡b = nothing
... | fgt b<a = just (pred a)

fcross≡fcross'
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
  → fcross b a ≡ fcross' b a
fcross≡fcross' fzero fzero = refl
fcross≡fcross' fzero (fsuc a) = refl
fcross≡fcross' (fsuc b) fzero = refl
fcross≡fcross' {x = suc x} (fsuc b) (fsuc a) with a ≤?ᶠ b 
... | fle a≤b =
  fcross (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (fcross b a)
    ≡⟨ cong fsuc (fcross≡fcross' b a) ⟩
  fsuc (fcross'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ fcross'-cases b a) (isPropDichotomyᶠ (a ≤?ᶠ b) (fle a≤b)) ⟩
  fsuc (fcross'-cases b a (fle a≤b))
    ≡⟨ refl ⟩
  fsuc (fin-restrict-≤ a a≤b)
    ≡⟨ refl ⟩
  fsuc (fin-restrict-< a (≤ᶠ→<ᶠ a≤b))
    ≡⟨ cong (fin-restrict-< (fsuc a)) (sym (fsuc≤fsuc→<fsuc a≤b) ) ⟩
  fin-restrict-< (fsuc a) (≤ᶠ→<ᶠ (fsuc≤fsuc a≤b))
    ≡⟨ refl ⟩
  fin-restrict-≤ (fsuc a) (fsuc≤fsuc a≤b)
    ≡⟨ refl ⟩
  fcross'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fle a≤b))
    ≡⟨ cong (fcross'-cases (fsuc b) (fsuc a))
            (isPropDichotomyᶠ (≤?ᶠ-suc (fle a≤b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  fcross'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
... | fgt a>b =
  fcross (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (fcross b a)
    ≡⟨ cong fsuc (fcross≡fcross' b a) ⟩
  fsuc (fcross'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ fcross'-cases b a) (isPropDichotomyᶠ (a ≤?ᶠ b) (fgt a>b)) ⟩
  fsuc (fcross'-cases b a (fgt a>b))
    ≡⟨ refl ⟩
  fsuc (pred a)
    ≡⟨ fsuc∘pred≡id {y = 1} (≉fsym (<ᶠ→≉ (≤<ᶠ-trans (fzero≤a b) a>b))) ⟩
  a
    ≡⟨ refl ⟩
  fcross'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fgt a>b))
    ≡⟨ cong (fcross'-cases (fsuc b) (fsuc a))
            (isPropDichotomyᶠ (≤?ᶠ-suc (fgt a>b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  fcross'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
