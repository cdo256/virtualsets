module VSet.Transform.Trace.Properties where

open import VSet.Prelude
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inverse.Base 
open import VSet.Transform.Inverse.Insert
open import VSet.Transform.Inverse.Properties
open import VSet.Transform.Trace.Base
open import VSet.Transform.Tensor.Base

private
  variable
    l l' m m' n n' : ℕ

remove-insert
  : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
  → (f : Inj m n)
  → remove a (insert a b f) ≡ f
remove-insert fzero b (nul _) = refl
remove-insert fzero b (inc c f) = refl
remove-insert (fsuc fzero) b (inc c f) =
  remove (fsuc fzero) (insert (fsuc fzero) b (inc c f))
    ≡⟨ refl ⟩
  remove (fsuc fzero) (inc (fsplice b c) (insert fzero (fcross c b) f))
    ≡⟨ refl ⟩
  remove (fsuc fzero) (inc (fsplice b c) (inc (fcross c b) f))
    ≡⟨ refl ⟩
  inc (fjoin (fsplice (fsplice b c) (fcross c b)) (fsplice b c)
          (≉fsym (fsplice≉b (fsplice b c) (fcross c b)))) f 
    ≡⟨ cong (λ ○ → inc ○ f) (fjoin-fsplice-fsplice-fcross-fsplice b c
       (≉fsym (fsplice≉b (fsplice b c) (fcross c b)))) ⟩ 
  inc (fjoin b (fsplice b c)
    (subst (_≉ᶠ_ (fsplice b c)) (fsplice-fsplice-fcross b c)
      (≉fsym (fsplice≉b (fsplice b c) (fcross c b))))) f 
    ≡⟨ cong (λ ○ → inc ○ f) (fjoin-fsplice-inverse b c _) ⟩
  inc c f ▯
remove-insert {m = suc m} {n = suc n} (fsuc a) b (inc c f) =
  let b' : Fin (suc n)
      b' = apply (insert a (fcross c b) f) a
  in
  remove (fsuc a) (insert (fsuc a) b (inc c f))
    ≡⟨ refl ⟩
  remove (fsuc a) (inc (fsplice b c) (insert a (fcross c b) f))
    ≡⟨ refl ⟩
  inc (fjoin (fsplice (fsplice b c) b') (fsplice b c)
                 (≉fsym (fsplice≉b (fsplice b c) b')))
      (remove a (insert a (fcross c b) f))
    ≡⟨ cong (inc _) (remove-insert a (fcross c b) f) ⟩
  inc (fjoin (fsplice (fsplice b c) b') (fsplice b c)
                 (≉fsym (fsplice≉b (fsplice b c) b'))) f
    ≡⟨ cong (λ ○ → inc ○ f) (fjoin-fsplice-fsplice-fsplice b b' c _) ⟩
  inc (fcross b' (fsplice b c)) f 
    ≡⟨ cong (λ ○ → inc (fcross ○ (fsplice b c)) f) (apply-insert≡b a (fcross c b) f) ⟩
  inc (fcross (fcross c b) (fsplice b c)) f 
    ≡⟨ cong (λ ○ → inc ○ f) (fcross-fcross-fsplice b c) ⟩
  inc c f ▯

tensor-trace-inverse : (l : ℕ) → (f : Inj m n) → trace l ((idInj l) ⊕ f) ≡ f
tensor-trace-inverse zero f = {!!}
tensor-trace-inverse (suc l) f = {!!}
