module VSet.Transform.Trace.Base where

open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inverse.Base 
open import VSet.Prelude

private
  variable
    l l' m m' n n' : ℕ

remove : ∀ {m n} → (a : Fin (suc m))
       → (f : Inj (suc m) (suc n)) → Inj m n
remove fzero (inc b f) = f
remove {suc m} {suc n} (fsuc a) (inc c f) =
  let b = apply f a
  in inc (fjoin (fsplice c b) c (≉fsym (fsplice≉b c b)))
         (remove a f) 

inverses
  : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
  → (f : Inj m n)
  → remove a (insert a b f) ≡ f
inverses fzero b (nul _) = refl
inverses fzero b (inc c f) = refl
inverses (fsuc fzero) b (inc c f) =
  remove (fsuc fzero) (insert (fsuc fzero) b (inc c f))
    ≡⟨ refl ⟩
  remove (fsuc fzero) (inc (fsplice b c) (insert fzero (fcross c b) f))
    ≡⟨ refl ⟩
  remove (fsuc fzero) (inc (fsplice b c) (inc (fcross c b) f))
    ≡⟨ refl ⟩
  inc (funsplice (fsplice (fsplice b c) (antisplice c b)) (fsplice b c)
          (≉fsym (fsplice≉b (fsplice b c) (antisplice c b)))) f 
    ≡⟨ cong (λ ○ → inc ○ f) (funsplice-irrelevant
         (fsplice (fsplice b c) (antisplice c b))
         (fsplice b c)
         (≉fsym (fsplice≉b (fsplice b c) (antisplice c b)))
         (≉fsym (fsplice≉b (fsplice b c) (antisplice c b)))) ⟩
  inc (funsplice (fsplice (fsplice b c) (antisplice c b)) (fsplice b c)
          (≉fsym (fsplice≉b (fsplice b c) (antisplice c b)))) f 
    ≡⟨ cong (λ ○ → inc ○ f) (funsplice-fsplice-fsplice-antisplice-fsplice b f c
       (≉fsym (fsplice≉b (fsplice b c) (antisplice c b)))) ⟩ 
  inc (funsplice b (fsplice b c)
    (subst (_≉ᶠ_ (fsplice b c)) (splice-splice-antisplice b c)
      (≉fsym (fsplice≉b (fsplice b c) (antisplice c b))))) f 
    ≡⟨ cong (λ ○ → inc ○ f) {!funsplice-fsplice-inverse b c {!subst (_≉ᶠ_ (fsplice b c)) (splice-splice-antisplice b c)
      (≉fsym (fsplice≉b (fsplice b c) (antisplice c b)))!}!} ⟩
  inc (funsplice b (fsplice b c)
    {!!}) f 
    ≡⟨ cong (λ ○ → inc ○ f) {!funsplice-fsplice-inverse {!b!} {!!}!} ⟩
  inc c f ▯
inverses (fsuc a) b (inc c f) =
  let b' = apply f {!!} in
  remove (fsuc a) (insert (fsuc a) b (inc c f))
    ≡⟨ refl ⟩
  remove (fsuc a) (inc (fsplice b c) (insert a (antisplice c b) f))
    ≡⟨ {!!} ⟩
  inc (funsplice (fsplice (fsplice b c) {!!}) (fsplice b c) {!!})
      {!!}
    ≡⟨ {!!} ⟩
  inc (fjoin (fsplice (fsplice b c) {!!}) {!!} (≉fsym (fsplice≉b {!!} {!!})))
      (remove {!!} {!!})
    ≡⟨ {!!} ⟩
  inc (fcross {!!} (fsplice b c)) (remove {!!} {!!})
    ≡⟨ {!!} ⟩
  inc c f ▯

trace1 : (f : Inj (suc m) (suc n)) → Inj m n
trace1 (inc fzero f) = f -- (0 x y z)
trace1 (inc (fsuc b) f) with apply-inv (inc (fsuc b) f) f0
... | nothing = f
... | just a = {!!}

trace : (l : ℕ) → (f : Inj (l + m) (l + n)) → Inj m n
trace = {!!}
