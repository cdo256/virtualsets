```
module Notes.TreeFin where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

```

## 2025-07-03

Okay, so I've got the following:

We currently have a definition of Fin using basic type formers:

```
SumFin : ℕ → Type
SumFin zero = ⊥
SumFin (suc n) = ⊤ ⊎ SumFin n
``` 

This is something that we can work with, but it would be convienient to be able to express the rules in Mark's preprint, for example to express the subtract operator.



```
```
