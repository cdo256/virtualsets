```agda
module Notes.InspectItDoesNothing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.Fin

inc : ∀ {X Y : ℕ} → Fin X ⊎ Fin Y → Fin (suc X) ⊎ Fin Y
inc (inl a) = inl (fsuc a)
inc (inr a) = inr a

+→⊎ : ∀ (X Y : ℕ) → Fin (X + Y) → Fin X ⊎ Fin Y
+→⊎ zero Y a = inr a
+→⊎ (suc X) Y a with fsplit a
... | inl _ = inl fzero
... | inr (a' , _) = inc (+→⊎ X Y a')

test-inspect
  : ∀ {X Y : ℕ} (u v : Fin (X + Y))
  → +→⊎ X Y u ≡ +→⊎ X Y v
  → u ≡ v
test-inspect {X} {Y} u v r
  with inspect (+→⊎ X Y) u | +→⊎ X Y u
... | [ p ]ᵢ | inl u' =
  let q : +→⊎ X Y u ≡ inl u'
      q = {!p!}
  in {!!}
... | [ p ]ᵢ | inr u' = {!!}
```
