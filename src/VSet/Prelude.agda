module VSet.Prelude where

open import Cubical.Foundations.Prelude public
open import Cubical.Core.Primitives public
open import Cubical.Foundations.Function public

open import Cubical.Data.Empty public renaming (elim to absurd)
open import Cubical.Data.Unit.Base public renaming (Unit to ⊤)
open import Cubical.Relation.Nullary public
open import Cubical.Data.Sum public

open import VSet.Path public
