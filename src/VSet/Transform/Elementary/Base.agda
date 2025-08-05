module VSet.Transform.Elementary.Base where

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

private
  variable
    l l' m m' n n' : ℕ

insert : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
       → (f : Inj m n) → Inj (suc m) (suc n)
insert fzero b f = inc b f
insert (fsuc a) b (inc c f) =
  inc (fsplice b c) (insert a (fcross c b) f)

-- Take out one element and shift everything over.
remove : ∀ {m n} → (a : Fin (suc m))
       → (f : Inj (suc m) (suc n)) → Inj m n
remove fzero (inc b f) = f
remove {suc m} {suc n} (fsuc a) (inc c f) =
  let b = apply f a
  in inc (fjoin (fsplice c b) c (≉fsym (fsplice≉b c b)))
         (remove a f) 

bubble : ∀ {m n} → (b : Fin (suc n))
       → (f : Inj m n) → Inj m (suc n)
bubble b (nul _) = nul _
bubble b (inc c f) =
  inc (fsplice b c) (bubble (fcross c b) f)

-- Remove from the domain without shifting the codomain.
excise : ∀ {m n} → (a : Fin (suc m))
       → (f : Inj (suc m) (suc n)) → Inj m (suc n)
excise a f = bubble (apply f a) (remove a f)
