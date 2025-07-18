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

## Top level

- Show that virtual sets form a Traced Monoidal Category
- Define VSet category
- Prove monoidal laws
  - Requires paths between members of equal types a : Fin i; b : Fin j.
- Prove trace laws
- Use the Int construction
- Prove composition is associative within the trace

## Funciton definitions

- Injection - Done
- Iso - Done
- Properties
  - ↣-map-⊎ - Done
  - _↣∘↣_ - Done
  - ↔to↣  - Done

## Path types

- `subst-inv` - subst is involutive. - Done

### Depdendent Paths

- reasoning syntax for dependent paths - Done, but causes unsolved metas when used.
  frustratingly not in cubical, but is in 1lab, so had to recreated it in my code

I had to fill in a lot of my knowledge about cubical type theory which took a day.

Given the complexity, I'm not sure that defining my morphism equality to be based on dependent paths was the best decision. It seemed natural to pick dependent paths in cubical agda becauase they're one of the main benefits that is given by cubical type theory, and they are very elegant in theory. Neither library provided satisfactory tooling to reason with dependent paths. That being said, the whole thing would be obviated if I switched to classical agda, as `x ≡ y` means that `a : Fin x` automatically gives that `a : Fin y` whenever the path can be computed.


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

### Explore Trees

Aborted

### Define SomeFin

This is the central abstraction around Nats and Fins

#### Minus operator on SomeFin - Done

To express removing a single element (for pred).
- Define minus operator 
- \­suc - Done
- \­pred - Done
- sa\0≡a - Done
- ins - Done
- |Fin1|≡1 - Done
- del - Done

#### Equality on SomeFin

Define ≈ as below: - Done
```agda
record _≈_ {A B X Y : ℕ} (f : [ A ↣ X ]) (g : [ B ↣ Y ]) : Type where
  field
    p : A ≡ B
    q : X ≡ Y
    path : (λ i → cong₂ FinFun p q i) [ fst f ≡ fst g ]
```

- Define _≈_ - Done
- Define ≈refl; ≈sym; ≈trans - Done
- Define reasoning syntax for ≈ - Done though could use some qol improvements.
- ≈transport - done
- ≈transport-fun - done, untested
- ≈transport-filler - done
- from≡ - done

#### Injection

Define abstraction for the basic category
- Define arrow - Done
- Define identity arrow - Done


## Transform


