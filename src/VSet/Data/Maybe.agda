module VSet.Data.Maybe where

open import VSet.Prelude
open import Cubical.Data.Maybe

mapMaybeNothing : ∀ {A B : Type} → {x : Maybe A} {f : A → B}
                → map-Maybe f x ≡ nothing → x ≡ nothing
mapMaybeNothing {x = nothing} map≡∅ = refl
mapMaybeNothing {x = just x} map≡∅ = absurd (¬just≡nothing map≡∅)
