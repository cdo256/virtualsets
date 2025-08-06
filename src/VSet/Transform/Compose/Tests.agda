module VSet.Transform.Compose.Tests where

open import VSet.Prelude

open import Cubical.Data.Nat
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base
open import VSet.Transform.Inverse.Insert
open import VSet.Transform.Elementary.Base
open import VSet.Transform.Compose.Base

-- Example injections:
f : Inj 2 4 -- (1 3)
f = inc f1 (inc f2 (nul 2))

g : Inj 4 4 -- (1 2 0)
g = cycle-l 3

h' = g ∘ʲ f

_ : apply h' f0 ≡ apply g (apply f f0)
_ = refl

_ : apply h' f1 ≡ apply g (apply f f1)
_ = refl

-- Test: ∘ʲ and ∘⁻ʲ are related
_ : (g ∘ʲ f) ≡ (f ∘⁻ʲ g)
_ = refl

-- Associativity-like test
h : Inj 4 5 -- (2 1 4 0)
h = inc f2 (inc f1 (inc f0 (inc f1 (nul 1))))

_ : apply (h ∘ʲ (g ∘ʲ f)) f0 ≡ apply ((h ∘ʲ g) ∘ʲ f) f0
_ = refl

_ : apply (h ∘ʲ (g ∘ʲ f)) f1 ≡ apply ((h ∘ʲ g) ∘ʲ f) f1
_ = refl
