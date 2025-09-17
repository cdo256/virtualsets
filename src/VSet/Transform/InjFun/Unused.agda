-- Functions proven but not currently needed
module VSet.Transform.InjFun.Unused where

open import VSet.Prelude
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import Cubical.Data.Nat.Properties

open import VSet.Data.Nat using (ℕ; zero; suc; _+_)
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.InjFun.Injection
open import VSet.Data.Fin.SumSplit using (⊎≅+)
open import VSet.Transform.InjFun.Pred

inc-func : ∀ {X Y : ℕ} → (⟦ X ⟧ → ⟦ Y ⟧) → (⟦ suc X ⟧ → ⟦ suc Y ⟧)
inc-func f fzero = fzero
inc-func f (fsuc x) = fsuc (f x)

inc-injective : ∀ {X Y : ℕ} → (f : [ X ↣ Y ])
              → is-injective (inc-func (fst f)) 
inc-injective (f , inj) fzero fzero f0≡f0 =
  refl
inc-injective (f , inj) fzero (fsuc y) f0≡fsy =
  absurd (fzero≢fsuc f0≡fsy)
inc-injective (f , inj) (fsuc x) fzero fsx≡f0 =
  absurd (fsuc≢fzero fsx≡f0) 
inc-injective (f , inj) (fsuc x) (fsuc y) shx≡shy =
  cong fsuc (inj x y (fsuc-injective shx≡shy))

inc : ∀ {X Y : ℕ} → [ X ↣ Y ] → [ suc X ↣ suc Y ]
inc f = inc-func (fst f) , inc-injective f

add : ∀ {X Y : ℕ} → (A : ℕ) → [ X ↣ Y ] → [ A + X ↣ A + Y ]
add {X} {Y} zero g = g
add {X} {Y} (suc A) g = inc (add A g)

+0r : ∀ {X Y : ℕ} → [ X ↣ Y ] → [ X + 0 ↣ Y + 0 ]
+0r {X} {Y} f = subst (λ ○ → [ ○ ↣ Y + 0 ]) (sym (+-zero X))
              $ subst (λ ○ → [ X ↣ ○ ]) (sym (+-zero Y)) f

dec-dom-func : ∀ {X Y : ℕ} → (⟦ suc X ⟧ → ⟦ Y ⟧) → (⟦ X ⟧ → ⟦ Y ⟧)
dec-dom-func {X} {Y} f a = f (fsuc a)

dec-dom-inj : ∀ {X Y : ℕ} → (f : [ suc X ↣ Y ])
            → is-injective (dec-dom-func (fst f))
dec-dom-inj {X} {Y} f a b ga≡gb = fsuc-injective (snd f (fsuc a) (fsuc b) ga≡gb)

dec-dom : ∀ {X Y : ℕ} → [ suc X ↣ Y ] → [ X ↣ Y ]
dec-dom {X} {Y} f = dec-dom-func (fst f) , dec-dom-inj f

join-dom-func : ∀ {X Y Z : ℕ}
              → (⟦ X ⟧ → ⟦ Z ⟧) → (⟦ Y ⟧ → ⟦ Z ⟧) → (⟦ X + Y ⟧ → ⟦ Z ⟧)
join-dom-func {zero} {Y} {Z} f g a = g a
join-dom-func {suc X} {Y} {Z} f g fzero = f fzero
join-dom-func {suc X} {Y} {Z} f g (fsuc a) =
  join-dom-func (f ∘ fsuc) g a

absurd-func : ∀ {A : Type} {X : ℕ} → (⟦ suc X ⟧ → ⟦ zero ⟧) → A
absurd-func {X} f with f fzero
... | ()

