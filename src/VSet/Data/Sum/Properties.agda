module VSet.Data.Sum.Properties where

open import VSet.Path
open import VSet.Prelude
open import VSet.Function.Base
open import VSet.Function.Iso
open import VSet.Function.Injection

open import Cubical.Data.Sum

inl≢inr : {A B : Type} → (a : A) → (b : B) → inl a ≢ inr b
inl≢inr {A} {B} a b p = subst P p tt
  where
    P : A ⊎ B → Type
    P (inl _) = ⊤
    P (inr _) = ⊥

inl-injective : {A B : Type} (x y : A) → inl x ≡ inl y → x ≡ y
inl-injective {A} {B} x y p = subst P p refl
  where
    P : A ⊎ B → Type
    P (inl a) = x ≡ a
    P (inr b) = ⊥

inr-injective : {A B : Type} (x y : B) → inr x ≡ inr y → x ≡ y
inr-injective {A} {B} x y p = subst P p refl
  where
    P : A ⊎ B → Type
    P (inl a) = ⊥
    P (inr b) = x ≡ b
