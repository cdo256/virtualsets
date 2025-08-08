module VSet.Transform.Trace.Base where

open import VSet.Prelude
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import VSet.Data.Fin.Base renaming (pred to fpred)
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

pred-cases : (f : Inj (suc m) (suc n))
           → (a'? : Maybe (Fin (suc (suc m)))) (b : Fin (suc n))
           → Inj (suc m) (suc n)
pred-cases f nothing b = f
pred-cases f (just fzero) b = f
pred-cases f (just (fsuc a)) b = insert a b (remove a f)

pred : (f : Inj (suc m) (suc n)) → Inj m n
pred {m = zero} (inc b f) = f
pred {m = suc m} {n = suc n} (inc fzero f) = f
pred {m = suc m} {n = suc n} (inc (fsuc b) f) =
  pred-cases f (apply-inv (inc (fsuc b) f) f0) b

trace : (l : ℕ) → (f : Inj (l + m) (l + n)) → Inj m n
trace zero f = f
trace (suc l) f = trace l (pred f)

infixl 30 trace
infixl 50 pred

syntax trace l f = f — l
syntax pred f = f —1
