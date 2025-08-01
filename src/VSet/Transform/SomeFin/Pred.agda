module VSet.Transform.SomeFin.Pred where

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
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Properties
open import VSet.Data.SomeFin.Injection
open import VSet.Data.SomeFin.Minus


module Pred {x y : SomeFin} (f : [ suc x ↣ suc y ]) where
  open _∖_
  f-inj : is-injective (fst f)
  f-inj = snd f

  g^ : ⟦ x ⟧ → ⟦ y ⟧
  g^ i =
    let (j — 0≢j) = ins fzero i 
    in del (fst f fzero) (fst f j — λ f0≡fj → 0≢j (f-inj fzero j f0≡fj))


  composition : (ai : (b₁ b₂ : ⟦ x ⟧) → val (ins fzero b₁) ≡ val (ins fzero b₂) → b₁ ≡ b₂)
       → (di : (B₁ B₂ : (suc y) ∖ fst f fzero)
             → del (fst f fzero) B₁ ≡ del (fst f fzero) B₂ → val B₁ ≡ val B₂)
       → is-injective g^
  composition ai di b₁ b₂ f'b₁≡f'b₂ =
    let
      (c₁ — z≢c₁) = ins fzero b₁
      (c₂ — z≢c₂) = ins fzero b₂
    in
    ai b₁ b₂
       (f-inj c₁ c₂
         (di (fst f c₁ — λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
             (fst f c₂ — λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
             f'b₁≡f'b₂))

  g-inj : is-injective g^
  g-inj b₁ b₂ gb₁≡gb₂ = 
    let
      ai : (b₁ b₂ : ⟦ x ⟧) → val (ins fzero b₁) ≡ val (ins fzero b₂) → b₁ ≡ b₂
      ai = ins-inj fzero
      di : (B₁ B₂ : (suc y) ∖ fst f fzero)
         → del (fst f fzero) B₁ ≡ del (fst f fzero) B₂
         → val B₁ ≡ val B₂
      di = del-inj (fst f fzero)
      (c₁ — z≢c₁) = ins fzero b₁
      (c₂ — z≢c₂) = ins fzero b₂
    in
    ai b₁ b₂
       (f-inj c₁ c₂
         (di (fst f c₁ — λ fz≡fc₁ → z≢c₁ (f-inj fzero c₁ fz≡fc₁))
             (fst f c₂ — λ fz≡fc₂ → z≢c₂ (f-inj fzero c₂ fz≡fc₂))
             gb₁≡gb₂))

  g : [ x ↣ y ]
  g = g^ , g-inj

open Pred using () renaming (g to pred) public

-- -}
