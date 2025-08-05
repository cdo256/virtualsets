module VSet.Transform.Trace.Base where

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
open import VSet.Transform.Elementary.Base

private
  variable
    l l' m m' n n' : ℕ

trace1-cases : (b : Fin (suc n)) → (f : Inj (suc m) (suc n))
             → (a'? : Maybe (Fin (suc (suc m))))
             → Inj (suc m) (suc n)
trace1-cases b f nothing = f
trace1-cases b f (just a') = insert (pred a') b (remove (pred a') f)

trace1 : (f : Inj (suc m) (suc n)) → Inj m n
trace1 {m = 0} _ = nul _
trace1 {m = suc m} (inc fzero f) = f
trace1 {m = suc m} {n = suc n} (inc (fsuc b) f) =
  trace1-cases b f (apply-inv (inc (fsuc b) f) f0)

trace : (l : ℕ) → (f : Inj (l + m) (l + n)) → Inj m n
trace zero f = f
trace (suc l) f = (trace l (trace1 f))
