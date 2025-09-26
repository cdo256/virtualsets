<!--
```
module Dissertation.InjCategory where

open import VSet.Prelude hiding (id)
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Compose.Properties
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties
```
-->

## Category Construction of `Inj`

We now have everything we need to construct a category simply by
satisfying all of the below requirements, we have:
 - Objects are `ℕ`.
 - Hom-sets are given by `Inj`
 - Identity is just `idInj` as defined above.
 - Then we have composition, we're defining it backwards, because
   that's that Agda's cubical library expects.
 - Left and right unitor laws.
 - Associativity, as we've just proven,
 - And isSetInj, to show the Hom-sets are really set-like.

```
open Category

InjCat : Category _ _
InjCat = record
  { ob = ℕ
  ; Hom[_,_] = Inj
  ; id = λ {n} → idInj n
  ; _⋆_ = _∘⁻ʲ_
  ; ⋆IdL = ∘ʲ-idR
  ; ⋆IdR = ∘ʲ-idL
  ; ⋆Assoc = λ x y z → ∘ʲ-assoc z y x
  ; isSetHom = isSetInj
  }
```

