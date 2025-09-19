module VSet.Transform.InjFun.Pred where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import VSet.Path
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.Nat
open import VSet.Data.Fin
open import VSet.Data.InjFun.Injection
open import VSet.Data.Fin.Minus

ins0 : {x : ℕ} → ⟦ x ⟧ → (suc x ∖ fzero)
ins0 a = s a —0

module Pred {x y : ℕ} (f' : [ suc x ↣ suc y ]) where
  open _∖_
  f = fst f'
  f-inj = snd f'

  g : ⟦ x ⟧ → ⟦ y ⟧
  g i =
    let f0≢fsi : f fzero ≢ f (fsuc i)
        f0≢fsi f0≡fsi = fzero≢fsuc (f-inj fzero (fsuc i) f0≡fsi) 
    in del (f fzero) (f (fsuc i) — f0≢fsi)

  g-inj : is-injective g
  g-inj b₁ b₂ gb₁≡gb₂ = 
    let
      (c₁ — z≢c₁) = s b₁ —0
      (c₂ — z≢c₂) = s b₂ —0
    in
    fsuc-injective {i = b₁} {j = b₂}
       (f-inj c₁ c₂
         (del-inj
           (f fzero)
           (f c₁ — λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
           (f c₂ — λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
           gb₁≡gb₂))

  g' : [ x ↣ y ]
  g' = g , g-inj

open Pred using () renaming (g' to pred) public
