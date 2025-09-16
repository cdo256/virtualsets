module VSet.Data.InjFun.Properties where

open import VSet.Prelude
open import VSet.Data.Fin
open import Cubical.Data.Nat.Properties
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.InjFun.Injection 
open import Cubical.Foundations.HLevels

isProp-is-injective : {m n : ℕ} → (f : Fin m → Fin n) → isProp (is-injective f)
isProp-is-injective {m} f = isPropΠ λ x → isPropΠ λ y → isProp→ (isSetFin x y)

isSetInjFun : {m n : ℕ} → isSet [ m ↣ n ]
isSetInjFun {m} {n} =
  isSetΣ (isSet→ isSetFin)
         (λ f → isProp→isSet (isProp-is-injective f))
