module VSet.Data.SomeFin.Base where

open import VSet.Prelude

import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.Nat.Base
  using (ℕ)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Data.Fin
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

SomeFin : Type
SomeFin = ℕ

⟦_⟧ : (n : SomeFin) → Type
⟦ n ⟧ = Fin n

infixl 8 _+_

_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y

record _∖_ (A : SomeFin) (a : Fin A) : Type where
  constructor _,_
  field
    val : Fin A
    ne : a ≢ val

open _∖_

ins : {x : ℕ} → (a : ⟦ suc x ⟧) → ⟦ x ⟧ → (suc x ∖ a)
ins {suc x} fzero b = fsuc b , fzero≢fsuc b
ins {suc x} (fsuc a) fzero = fzero , fsuc≢fzero a
ins {suc x} (fsuc a) (fsuc b) =
  fsuc c , λ sa≡sc →
    let a≡c = fsuc-injective {suc x} {a} {c} sa≡sc
    in ne (ins a b) a≡c
  where
    c = val (ins a b)

|Fin1|≡1 : (a b : ⟦ 1 ⟧) → a ≡ b
|Fin1|≡1 = isContr→isProp (fzero , f)
  where
    f : (y : ⟦ 1 ⟧) → fzero ≡ y
    f fzero = refl

del : {x : ℕ} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
del {ℕ.zero} fzero (fzero , 0≢0) = absurd (0≢0 refl)
del {suc x} fzero (fzero , 0≢0) = absurd (0≢0 refl)
del {suc x} fzero (fsuc b , a≢b) = b
del {suc x} (fsuc a) (fzero , a≢b) = fzero
del {suc x} (fsuc a) (fsuc b , a'≢b') =
  fsuc (del {x} a (b , λ a≡b → absurd (a'≢b' (cong fsuc a≡b))))

