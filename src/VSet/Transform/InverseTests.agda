module VSet.Transform.InverseTests where

open import VSet.Prelude
open import Cubical.Data.Nat.Base hiding (elim)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice 
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 
open import Cubical.Data.List
open import VSet.Transform.Inverse

g1 : Inj 2 3
g1 = (inc f2 $ inc f0 $ nul 1) 

_ : (inc f3 $ inc f1 $ inc f0 $ nul 1) ≡ insert f2 f0 g1
_ = refl

_ : apply (insert f2 f0 g1) f2 ≡ f0
_ = refl

_ : apply (insert f0 f2 (idInj 2)) f1 ≡ fsplice f2 (apply (idInj 2) (antisplice f0 f1))
_ = refl

_ : apply (insert f0 f2 (idInj 2)) f2 ≡ fsplice f2 (apply (idInj 2) (antisplice f0 f2))
_ = refl

_ : apply (insert f0 f2 (idInj 2)) f2 ≡ fsplice f2 (apply (idInj 2) (antisplice f0 f2))
_ = refl

_ : apply (insert f1 f0 (idInj 2)) f0 ≡ fsplice f0 (apply (idInj 2) (antisplice f1 f0))
_ = refl

_ : apply (insert f1 f0 (idInj 2)) f1 ≡ f0
_ = refl

_ : apply (insert f1 f0 (idInj 2)) f2 ≡ fsplice f0 (apply (idInj 2) (antisplice f1 f2))
_ = refl

_ : apply (insert f1 f2 cross) f1 ≡ f2
_ = refl

_ : apply (insert f1 f2 cross) f0 ≡ fsplice f2 (apply cross (antisplice f1 f0))
_ = refl

_ : apply (insert f1 f2 cross) f2 ≡ fsplice f2 (apply cross (antisplice f1 f2))
_ = refl

-- (1 2 4 0)
g2 : Inj 4 5
g2 = (inc f1 $ inc f1 $ inc f2 $ inc f0 $ nul 1)

_ : insert f1 f3 g2 ≡ (inc f1 $ inc f2 $ inc f1 $ inc f2 $ inc f0 $ nul 1)
_ = refl

_ : to-list (insert f1 f3 g2) ≡ f1 ∷ f3 ∷ f2 ∷ f5 ∷ f0 ∷ []
_ = refl

_ : apply (insert f1 f3 g2) f2 ≡ fsplice f3 (apply g2 (antisplice f1 f2))
_ = refl

_ : apply (insert f4 f3 g2) f2 ≡ fsplice f3 (apply g2 (antisplice f4 f2))
_ = {!!}

w = (antisplice f4 f2)


-- insert 4 3 (1 2 4 0) ≡ (1 2 5 0 3)
_ : apply (insert f4 f3 g2) f2 ≡ {!!}
_ = {!!}

_ : antisplice {x = 4} f4 f2 ≡ f2
_ = refl
