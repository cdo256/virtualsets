module VSet.Data.SomeFin.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Core.Primitives
import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.Nat.Base
  using (ℕ)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.SumFin.Base
open import Cubical.Data.SumFin.Properties

open import VSet.Path
open import VSet.Data.Fin.Default
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
ins = {!!}
-- ins {suc x} a b with fin-view a | fin-view b
-- ... | vzero | _ = fsuc b , fzero≠fsuc
-- ... | vsuc a | vzero = fzero , (fsuc≠fzero)
-- ... | vsuc a | vsuc b with ins a b
-- ... | i , a≢i = fsuc i , (λ a'≡i' → a≢i (fsuc-inj a'≡i'))

|Fin1|≡1 : (a b : ⟦ 1 ⟧) → a ≡ b
|Fin1|≡1 = isContr→isProp isContrSumFin1

del : {x : ℕ} → (a : ⟦ suc x ⟧) → (suc x ∖ a) → ⟦ x ⟧
del = {!!}
-- del {zero} a (b , b≢a) = absurd (b≢a (|Fin1|≡1 a b))
-- del {suc x} a (b , b≢a) with fin-view a | fin-view b
-- ... | vzero | vzero = absurd (b≢a refl)
-- ... | vzero | vsuc b = b
-- ... | vsuc a | vzero = fzero
-- ... | vsuc a | vsuc b with del a (b , (λ a≡b → b≢a (ap fsuc a≡b)))
-- ... | i = fsuc i
