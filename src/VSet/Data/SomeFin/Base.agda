module VSet.Data.SomeFin.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Core.Primitives
import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.Nat.Base
  using (ℕ)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import VSet.Path
open import VSet.Data.Fin.Base
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

SomeFin : Type
SomeFin = ℕ

⟦_⟧ : (n : SomeFin) → Type
⟦ n ⟧ = Fin n

infixl 8 _+_

pattern zero = ℕ.zero
pattern suc X = ℕ.suc X

_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y



record _∖_ (A : SomeFin) (a : Fin A) : Type where
  constructor _,_
  field
    val : Fin A
    .≠ : a ≢ val

open _∖_

ins : {x : ℕ} → (a : ⟦ suc x ⟧) → ⟦ x ⟧ → (suc x ∖ a)
ins {suc x} fzero b = fsuc b , {!fzero≢fsuc!}
ins {suc x} (fsuc a) fzero = fzero , {!!}
ins {suc x} (fsuc a) (fsuc b) =
  let
    (c , a≢c) = ins a b
  in fsuc (val (ins a b)) , λ a'≡c' → a≢c ({!suc-injective!} a'≡c')


|Fin1|≡1 : (a b : ⟦ 1 ⟧) → a ≡ b
|Fin1|≡1 = isContr→isProp {!isContrSumFin1!}

del : {x : ℕ} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
del {ℕ.zero} fzero (fzero , 0≢0) = absurd {!0≢0 refl!}
del {suc x} fzero (fzero , 0≢0) = absurd {!0≢0 refl!}
del {suc x} fzero (fsuc b , a≢b) = b
del {suc x} (fsuc a) (fzero , a≢b) = fzero
del {suc x} (fsuc a) (fsuc b , a'≢b') =
  fsuc (del {x} a (b , λ a≡b → absurd (a'≢b' (cong fsuc a≡b))))

