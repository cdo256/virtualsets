```
module Notes.ToDo where

open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties

open import VSet.Prelude
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection

open import Cubical.Foundations.Equiv.Base 
```

## Data

### Fin

- Redefine Fin in the standard library way - Done
- Fin; fzero; fsuc - Done
- elim; toℕ; fromℕ; pred - Done
- fshift; finject - Done
- fzero≢fsuc; - fsuc≢fzero - Done
- Fin0≃⊥ - Done
- toℕ∘fromℕ≡id - Done
- toℕ<m - Done
- fromℕ∘toℕ≡id - Done
- fsuc-injective - Done except for y=0 case.
- finject-injective - Done
- finject∘fsuc-commutes - Done
- fshift-injective  - Done

### Nat

- ¬-<-zero - Done
- pred-<-pred - Done
- suc-<-suc - Done

## Transformations on Inj

### Elementary

Define elementary operations:
- insert - Done
- remove - Done
- bubble - Done
- excise - Done

## Cat

### Base

- Construct VSetCat.

### Monoidal

- Show _⊕_ is a bifunctor - In progress
  - Show _⊕_ preserves composition - In progress
- Show idenity triangle commutes.
- Show monoidal pentagon commutes.
- Show _⊕_ is symmetric.

### Traced

- Tightening
- Sliding
- Vanishing - Sketched
- Strength - WIP

### Compact Closed

- Dual construciton
