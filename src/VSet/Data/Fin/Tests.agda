module VSet.Data.Fin.Tests where

open import VSet.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import VSet.Data.Nat.Order
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties

open ℕ.ℕ

private
  variable
    ℓ : Level
    x y : ℕ

--module Test-fsplice where
  -- expected: f1 , f2 , f0 , f2
t0 : Fin 3 × Fin 3 × Fin 3 × Fin 3
t0 = fsplice' f0 f0
   , fsplice' f0 f1
   , fsplice' f1 f0
   , fsplice' f1 f1

t1 : Fin 2 × Fin 2 × Fin 2 × Fin 2
t1 = funsplice' f0 (fsplice f0 f0) (fsplice≢b f0 f0)
   , funsplice' f0 (fsplice f0 f1) (fsplice≢b f0 f1)
   , funsplice' f1 (fsplice f1 f0) (fsplice≢b f1 f0)
   , funsplice' f1 (fsplice f1 f1) (fsplice≢b f1 f1)
