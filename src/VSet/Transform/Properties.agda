module VSet.Transform.Properties where

open import VSet.Prelude
open import VSet.Data.Fin hiding (pred)

open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Sub
open import VSet.Transform.Add
open import VSet.Transform.Pred

lemma1-3 : ∀ (X Y A : SomeFin) → (f : [ X ↣ Y ])
         → sub A (add A f) ≡ f
lemma1-3 X Y zero f = refl
lemma1-3 X Y (suc A) f =
  sub (suc A) (add (suc A) f) ≡⟨ {!!} ⟩
  sub (suc A) (add (suc A) f) ≡⟨ {!!} ⟩
  f ∎

lemma1-4 : ∀ (X Y A B : SomeFin) → (f : [ A + X ↣ A + Y ])
         → add B (sub A f) ≡ sub A {!add B f!} 
