module VSet.Prelude where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Transport public hiding (transpEquiv)
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Core.Primitives public

open import Cubical.Data.Equality.Base public using (id)
open import Cubical.Data.Empty public renaming (elim to absurd)
open import Cubical.Data.Unit.Base public renaming (Unit to ⊤)
open import Cubical.Relation.Nullary public
open import Cubical.Data.Prod public
open import Cubical.Data.Sum public
  renaming (rec to ⊎-rec; elim to ⊎-elim; map to ⊎-map)


open import VSet.Path public
