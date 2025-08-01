module VSet.Transform.Compose.Tests where

open import VSet.Prelude

open import Cubical.Data.Nat
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base
open import VSet.Transform.Inverse.Insert

a : Fin 2
a = fzero

b : Fin 3
b = fsuc fzero

f : Inj 1 1
f = idInj 1

x : Fin 2
x = fsuc fzero

c : Fin 2
c = fzero

x'≉a' : fsuc x ≉ᶠ fsuc a
x'≉a' (≈fsuc ())

fsplice-lemma1T
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc (suc m))) → (f : Inj m m)
  → (x : Fin (suc m)) → (c : Fin (suc m)) → (x'≉a' : fsuc x ≉ᶠ fsuc a)
  → Type
fsplice-lemma1T a b f x c x'≉a' =
    fsplice (fsplice b c) (apply-insert a (antisplice c b) f x (x ≈?ᶠ a)) 
  ≡ fsplice b (apply (inc c f) (fsuc (funsplice a x (≉pred x'≉a')))) 


test-fsplice-lemma1 : fsplice-lemma1T a b f x c x'≉a'
test-fsplice-lemma1 = refl

_ : fsplice-lemma1T f0 f1 (idInj 1) f1 f0 (≉fsuc (λ ()))
_ = refl
_ : fsplice-lemma1T f1 f2 (idInj 1) f0 f1 (≉fsuc (λ()))
_ = refl

_ : fsplice-lemma1T f1 f2 (idInj 2) f0 f2 (≉fsuc (λ()))
_ = refl

_ : fsplice-lemma1T f2 f1 (idInj 2) f0 f1 (≉fsuc (λ()))
_ = refl

_ : fsplice-lemma1T f0 f3 (idInj 2) f1 f2 (≉fsuc (λ()))
_ = refl

_ : fsplice-lemma1T f1 f3 (idInj 2) f2 f0 (≉fsuc (≉fsuc λ()))
_ = refl

_ : fsplice-lemma1T f2 f2 (idInj 2) f1 f1 (≉fsuc (≉fsuc λ()))
_ = refl

_ : fsplice-lemma1T f1 f4 (idInj 3) f3 f2 (≉fsuc (≉fsuc λ()))
_ = refl

_ : fsplice-lemma1T f3 f3 (idInj 3) f2 f1 (≉fsuc (≉fsuc (≉fsuc λ())))
_ = refl

_ : fsplice-lemma1T f2 f4 (idInj 3) f0 f3 (≉fsuc (λ()))
_ = refl
