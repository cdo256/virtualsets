-- Functions proven but not currently needed
module VSet.Transform.SomeFin.Unused where

open import VSet.Prelude
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import Cubical.Data.Nat.Properties

open import VSet.Data.Nat using (ℕ; zero; suc)
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Data.SomeFin.Properties
open import VSet.Transform.SomeFin.Split using (⊎↔+)
open import VSet.Transform.SomeFin.Pred

inc-func : ∀ {X Y : SomeFin} → (⟦ X ⟧ → ⟦ Y ⟧) → (⟦ suc X ⟧ → ⟦ suc Y ⟧)
inc-func f fzero = fzero
inc-func f (fsuc x) = fsuc (f x)

inc-injective : ∀ {X Y : SomeFin} → (f : [ X ↣ Y ])
              → is-injective (inc-func (fst f)) 
inc-injective (f , inj) fzero fzero f0≡f0 =
  refl
inc-injective (f , inj) fzero (fsuc y) f0≡fsy =
  absurd (fzero≢fsuc (f y) f0≡fsy)
inc-injective (f , inj) (fsuc x) fzero fsx≡f0 =
  absurd (fsuc≢fzero (f x) fsx≡f0) 
inc-injective (f , inj) (fsuc x) (fsuc y) shx≡shy =
  cong fsuc (inj x y (fsuc-injective shx≡shy))

inc : ∀ {X Y : SomeFin} → [ X ↣ Y ] → [ suc X ↣ suc Y ]
inc f = inc-func (fst f) , inc-injective f

add : ∀ {X Y : SomeFin} → (A : SomeFin) → [ X ↣ Y ] → [ A + X ↣ A + Y ]
add {X} {Y} zero g = g
add {X} {Y} (suc A) g = inc (add A g)

+0r : ∀ {X Y : SomeFin} → [ X ↣ Y ] → [ X + 0 ↣ Y + 0 ]
+0r {X} {Y} f = subst (λ ○ → [ ○ ↣ Y + 0 ]) (sym (+-zero X))
              $ subst (λ ○ → [ X ↣ ○ ]) (sym (+-zero Y)) f

dec-dom-func : ∀ {X Y : SomeFin} → (⟦ suc X ⟧ → ⟦ Y ⟧) → (⟦ X ⟧ → ⟦ Y ⟧)
dec-dom-func {X} {Y} f a = f (fsuc a)

dec-dom-inj : ∀ {X Y : SomeFin} → (f : [ suc X ↣ Y ])
            → is-injective (dec-dom-func (fst f))
dec-dom-inj {X} {Y} f a b ga≡gb = fsuc-injective (snd f (fsuc a) (fsuc b) ga≡gb)

dec-dom : ∀ {X Y : SomeFin} → [ suc X ↣ Y ] → [ X ↣ Y ]
dec-dom {X} {Y} f = dec-dom-func (fst f) , dec-dom-inj f

join-dom-func : ∀ {X Y Z : SomeFin}
              → (⟦ X ⟧ → ⟦ Z ⟧) → (⟦ Y ⟧ → ⟦ Z ⟧) → (⟦ X + Y ⟧ → ⟦ Z ⟧)
join-dom-func {zero} {Y} {Z} f g a = g a
join-dom-func {suc X} {Y} {Z} f g fzero = f fzero
join-dom-func {suc X} {Y} {Z} f g (fsuc a) =
  join-dom-func (f ∘ fsuc) g a

absurd-func : ∀ {A : Type} {X : SomeFin} → (⟦ suc X ⟧ → ⟦ zero ⟧) → A
absurd-func {X} f with f fzero
... | ()

