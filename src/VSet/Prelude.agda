module VSet.Prelude where

open import Cubical.Foundations.Prelude public renaming (_∎ to _▯)
open import Cubical.Foundations.Function public hiding (flip)
open import Cubical.Foundations.Transport public hiding (transpEquiv)
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Core.Primitives public
open import Agda.Primitive public

open import Cubical.Data.Equality.Base public using (id)
open import Cubical.Data.Empty public renaming (rec to absurd) hiding (elim)
open import Cubical.Data.Unit.Base public renaming (Unit to ⊤)
open import Cubical.Relation.Nullary public
open import Cubical.Data.Prod hiding (map) public
open import Cubical.Data.Sum public
  renaming (rec to ⊎-rec; elim to ⊎-elim; map to ⊎-map)

open import VSet.Path public

infix 12 _≅_
_≅_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
_≅_ = Iso
