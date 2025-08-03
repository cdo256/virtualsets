module VSet.Transform.Inverse.Base where

open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Prelude

private
  variable
    l l' m m' n n' : ℕ

apply-inv-rec : {m n : ℕ} → (f : Inj m n) → (b y : Fin (suc n)) → Dec (y ≈ᶠ b) → Maybe (Fin (suc m))
apply-inv : {m n : ℕ} → (f : Inj m n) → (y : Fin n) → Maybe (Fin m)

apply-inv-rec f b y (yes y≈b) = just fzero
apply-inv-rec f b y (no y≉b) =
  map-Maybe fsuc (apply-inv f (fjoin b y y≉b))

apply-inv (nul _) _ = nothing
apply-inv (inc b f) y = apply-inv-rec f b y (y ≈?ᶠ b)

insert : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
       → (f : Inj m n) → Inj (suc m) (suc n)
insert fzero b f = inc b f
insert (fsuc a) b (inc c f) =
  inc (fsplice b c) (insert a (fcross c b) f)

inv : ∀ {m} → (f : Inj m m) → Inj m m
inv {zero} (nul zero) = nul zero
inv {suc m} (inc c f) = insert c fzero (inv f)
