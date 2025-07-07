module VSet.Data.Sum.Properties where

open import VSet.Path
open import VSet.Prelude
open import VSet.Function.Base
open import VSet.Function.Iso
open import VSet.Function.Injection

open import Cubical.Data.Sum

private
  variable
    A B C D : Type

inl≢inr : {A B : Type} → (a : A) → (b : B) → inl a ≢ inr b
inl≢inr {A} {B} a b p = transport (cong P p) tt
  where
    P : A ⊎ B → Type
    P (inl _) = ⊤
    P (inr _) = ⊥

inl-injective : {A B : Type} (x y : A) → inl x ≡ inl y → x ≡ y
inl-injective {A} {B} x y p i =
  case p i of λ
    { (inl a) → a
    ; (inr b) → absurd (inl≢inr x b λ j → p {!i ∧ j!})
    }

inr-injective : {A B : Type} (x y : A) → inr x ≡ inr y → x ≡ y
inr-injective x y p i =
  case p i of λ
    { (inl a) → {!!}
    ; (inr b) → b
    }
