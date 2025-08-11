module VSet.Transform.FinFun.Compose where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.FinFun.Injection
open import VSet.Transform.FinFun.Pred

infixl 8 _⊙_

_⊙_ : ∀ {X Y Z} → [ Y ↣ Z ] → [ X ↣ Y ] → [ X ↣ Z ]
_⊙_ g f = (fst g ∘ fst f) , λ x y z → f .snd x y (g .snd (f .fst x) (f .fst y) z)

⊙IdR : {X Y : ℕ} (f : [ X ↣ Y ]) → (f ⊙ id↣) ≡ f
⊙IdR = {!!}
