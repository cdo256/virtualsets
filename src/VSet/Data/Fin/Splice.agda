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
fsplice' : ∀ {x : ℕ} → Fin (suc x) → Fin x → Fin (suc x)
fsplice' b a with b ≤?ᶠ finj a
... | fle b≤a = fsuc a
... | fgt a<b = finj a

antisplice : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
           → Fin (suc x)
antisplice _ fzero = fzero
antisplice fzero (fsuc a) = a
antisplice {suc x} (fsuc b) (fsuc a) =
  fsuc (antisplice b a)

antisplice' : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
           → Fin (suc x)
antisplice' b a with a ≟ᶠ finj b
antisplice' b a | flt a<b = fin-restrict a a<b
antisplice' b a | feq a≡b = b
antisplice' b (fsuc a) | fgt a>b = a

-- Remove a from domain of b
funsplice : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc x)) → a ≢ b
          → Fin x 
funsplice {x = zero} fzero fzero 0≢0 = absurd (0≢0 refl)
funsplice {x = suc zero} _ _ _ = fzero
funsplice {x = suc (suc x)} _ fzero _ = fzero
funsplice {x = suc (suc x)} fzero (fsuc a) _ = a
funsplice {x = suc (suc x)} (fsuc b) (fsuc a) a'≢b' =
  fsuc (funsplice b a λ a≡b → a'≢b' (cong fsuc a≡b))

-- Alternate definition
funsplice' : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x))) → a ≢ b
           → Fin (suc x)
funsplice' b a a≢b with a ≟ᶠ b
... | flt a<b = fin-restrict a a<b
... | feq a≡b = absurd (a≢b a≡b)
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
