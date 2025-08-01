module VSet.Data.Fin.Tests where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties

open ℕ.ℕ

private
  variable
    ℓ : Level
    x y : ℕ

t0 : Fin 3 × Fin 3 × Fin 3 × Fin 3
t0 = fsplice f0 f0
   , fsplice f0 f1
   , fsplice f1 f0
   , fsplice f1 f1
_ : t0 ≡ (f1 , f2 , f0 , f2)
_ = refl

t1 : Fin 2 × Fin 2 × Fin 2 × Fin 2
t1 = funsplice f0 (fsplice f0 f0) (fsplice≉b f0 f0)
   , funsplice f0 (fsplice f0 f1) (fsplice≉b f0 f1)
   , funsplice f1 (fsplice f1 f0) (fsplice≉b f1 f0)
   , funsplice f1 (fsplice f1 f1) (fsplice≉b f1 f1)
_ : t1 ≡ (f0 , f1 , f0 , f1)
_ = refl

t2 : Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2
t2 = antisplice' f0 f0 -- eq
   , antisplice' f0 f1 -- pred
   , antisplice' f0 f2 -- pred
   , antisplice' f1 f0 -- eq
   , antisplice' f1 f1 -- eq
   , antisplice' f1 f2 -- pred
_ : t2 ≡ (f0 , f0 , f1 , f0 , f1 , f1)
_ = refl
