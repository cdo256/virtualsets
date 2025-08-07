module VSet.Transform.Elementary.Properties where

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
open import VSet.Transform.Elementary.Base

private
  variable
    l l' m m' n n' : ℕ

apply-remove
  : ∀ {m n : ℕ} → (f : Inj (suc m) (suc n)) (a : Fin (suc m)) (b : Fin m)
  → apply (remove a f) b ≡ {!!}
apply-remove {suc m} {zero} (inc b ())
apply-remove {suc m} {suc n} (inc c f) fzero b =
  apply (remove f0 (inc c f)) b
    ≡⟨ refl ⟩
  apply f b
    ≡⟨ {!!} ⟩
  fsplice {!!} {!!}
    ≡⟨ {!!} ⟩
  {!!} ▯
apply-remove {suc m} {suc n} (inc c f) (fsuc a) fzero =
  apply (remove (fsuc a) (inc c f)) fzero
    ≡⟨ refl ⟩
  apply (inc (fcross (apply f a) c) (remove a f)) fzero 
    ≡⟨ refl ⟩
 fcross (apply f a) c 
    ≡⟨ {!!} ⟩
  {!!} ▯
apply-remove {suc m} {suc n} (inc c f) (fsuc a) (fsuc b) =
  apply (remove (fsuc a) (inc c f)) (fsuc b)
    ≡⟨ refl ⟩
  apply (inc (fcross (apply f a) c) (remove a f)) (fsuc b)
    ≡⟨ refl ⟩
  fsplice (fcross (apply f a) c) (apply (remove a f) b)
    ≡⟨ {!!} ⟩
  {!!} ▯


-- fcross-
--   →  fcross (apply (inc (fcross c b) f) fzero) (fsplice b c)
--   ≡ fjoin (fsplice (fsplice b c) (fcross c b)) (fsplice b c)
--         (≉fsym (fsplice≉b (fsplice b c) (fcross c b)))
