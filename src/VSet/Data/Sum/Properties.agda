module VSet.Data.Sum.Properties where

open import VSet.Path
open import VSet.Prelude
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

⊎-map-id≡id : {A B : Type} → ⊎-map (id {A = A}) (id {A = B}) ≡ id 
⊎-map-id≡id {A = A} {B} = funExt e
  where
    e : (x : A ⊎ B) → ⊎-map id id x ≡ id x
    e (inl x) = refl
    e (inr x) = refl

⊎-map-∘ : {A A' A'' B B' B'' : Type}
        → (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
        → ⊎-map f' g' ∘ ⊎-map f g ≡ ⊎-map (f' ∘ f) (g' ∘ g)
⊎-map-∘ f f' g g' = funExt e
  where
    e : (x : _) →
         (⊎-map f' g' ∘ ⊎-map f g) x ≡ ⊎-map (f' ∘ f) (g' ∘ g) x
    e (inl x) = refl
    e (inr x) = refl

⊎-assoc : {A B C : Type} → A ⊎ (B ⊎ C) ≅ (A ⊎ B) ⊎ C
⊎-assoc = record
  { fun = f
  ; inv = g
  ; leftInv = retr
  ; rightInv = sect
  }
  where
    f : {A B C : Type} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
    f (inl a) = inl (inl a)
    f (inr (inl b)) = inl (inr b)
    f (inr (inr c)) = inr c
    g : {A B C : Type} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C) 
    g (inl (inl a)) = inl a
    g (inl (inr b)) = inr (inl b)
    g (inr c) = inr (inr c)
    sect : section f g
    sect (inl (inl a)) = refl
    sect (inl (inr b)) = refl
    sect (inr c) = refl
    retr : retract f g
    retr (inl a) = refl
    retr (inr (inl b)) = refl
    retr (inr (inr c)) = refl
