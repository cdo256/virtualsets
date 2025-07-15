```
module Notes.ToDo where
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

Helpers:
- `subst-inv` - subst is involutive. - Done

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
- fsuc-injective - Done
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

- Central abstraction around Nats and Fins - Done

#### Minus operator
To express removing a single element (for pred).
- Define minus operator 
- \­suc - Done
- \­pred - Done
- sa\0≡a - Done
- ins - Done
- |Fin1|≡1 - Done
- del - Done

#### Injection
Define abstraction for the basic category
- Define arrow
- Define identity arrow
- Define equivalence
