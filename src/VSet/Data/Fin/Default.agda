module VSet.Data.Fin.Default where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin as ℕ
open import Cubical.Data.Fin.Properties

open import VSet.Path

fsuc≢fzero : {x : ℕ} → (a : Fin x) → fsuc a ≢ fzero
fsuc≢fzero (a , a<x) sa≡0 = snotz (cong toℕ sa≡0)

fzero≢fsuc : {x : ℕ} → (a : Fin x) → fzero ≢ fsuc a
fzero≢fsuc (a , a<x) 0≡sa = znots (cong toℕ 0≡sa)
