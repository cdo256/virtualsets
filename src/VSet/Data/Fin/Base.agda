module VSet.Data.Fin.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives

open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import VSet.Path
open import VSet.Data.Tree.Base

private
  variable
    ℓ : Level

Fin : ℕ → Type
Fin zero = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

Fin→ℕ : {x : ℕ} → Fin x → ℕ
Fin→ℕ {suc x} (inl _) = zero
Fin→ℕ {suc x} (inr a) = suc (Fin→ℕ a)

t : Tree
t = (fork (fork leaf leaf) leaf) 

t# : Tree# 3
t# = t , refl

x : ⟦ t ⟧
x = inl (inr tt)

fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x + y)
fshift zero a = a
fshift (suc x) a = inr (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x + y)
finject {x} zero a = subst Fin (sym (+-zero x)) a
finject {suc x} (suc y) (inl tt) = inl tt
finject {suc x} (suc y) (inr a) = inr (finject {x} (suc y) a)

caseTree : ∀ {ℓ} → {A : Type ℓ} → (al af : A) → Tree → A
caseTree al af leaf = al
caseTree al af (fork t1 t2) = af

fork≢leaf : {t1 t2 : Tree} → fork t1 t2 ≢ leaf
fork≢leaf {t1} {t2} f≡l = subst (caseTree ⊥ Tree) f≡l leaf

leaf≢fork : {t1 t2 : Tree} → leaf ≢ fork t1 t2 
leaf≢fork {t1} {t2} f≡l = subst (caseTree Tree ⊥) f≡l leaf 

non-zero : (t : Tree) → ∥ t ∥ ≥ 1
non-zero leaf = suc-≤-suc zero-≤
non-zero (fork t₁ t₂) = ≤-trans ge1 ≤SumLeft
  where
    ge1 = non-zero t₁

fork>leaf : {t1 t2 : Tree} → (∥ fork t1 t2 ∥) > (∥ leaf ∥)
fork>leaf {t1} {t2} = <≤-trans 2>1 fork≥2
  where
    ge1 = non-zero t1
    ge2 = non-zero t2
    fork≥2 : (∥ fork t1 t2 ∥) ≥ 2
    fork≥2 = ≤-trans (suc-≤-suc ge2) (≤-+k ge1)
    2>1 : 2 > 1
    2>1 = 0 , refl

∥fork∥≢∥leaf∥ : {t1 t2 : Tree} → (∥ fork t1 t2 ∥) ≢ (∥ leaf ∥)
∥fork∥≢∥leaf∥ = (<→≢ {!fork>leaf!})

reassoc : (t1 t2 : Tree) → ∥ t1 ∥ ≡ ∥ t2 ∥ → ⟦ t1 ⟧ → ⟦ t2 ⟧
reassoc leaf leaf p tt = tt
reassoc leaf (fork t2 t3) p a =
  {!!}
reassoc (fork t1 t3) t2 p a = {!!}

norm : (t : Tree) → ⟦ t ⟧ → Σ ℕ Fin
norm leaf a = 1 , inl tt
norm (fork t1 t2) (inl a1) = ∥ t1 ∥ + ∥ t2 ∥ , {!!}
norm (fork t1 t2) (inr a1) = ∥ t1 ∥ + ∥ t2 ∥ , {!!}
  -- where
  --   a1 : Fin ∥ t1 ∥
  --   a1 = snd (norm t1 )

neg : (x : ℕ) → (a : Fin x) → Fin x 
neg (suc x) (inl _) = inl tt
neg (suc x) (inr a) = {!!}
  where f : (x : ℕ) → (a : Fin (suc x)) → Fin x → Fin x
        f x a b = {!!}

-- Tree# : ℕ → Type
-- Tree# zero = ⊤
-- Tree# (suc x) = Σ[ a ∈ Fin x ] {!Tree# (Fin→ℕ a) × Tree# (Fin→ℕ (neg x a))!}

-- Tree : ℕ → Type
-- Split : {x : ℕ} → Fin x → Tree → Tree → Tree
-- Split {suc x} (inl _) c = Tree (Fin→ℕ {!!})
-- Split {suc x} (inr a) = {!!}
-- Tree zero = ⊤
-- Tree (suc n) = Σ (Fin n) {!!}

{-
module Tree (M : ℕ) where

  ℕ→Fin : (x : ℕ) → Fin (suc x)
  ℕ→Fin = ?

  _+ꟳ_ : {x : ℕ} → Fin → Fin 

  inv : {x : ℕ} → (y : Fin x) → (a : Fin y) → Σ[ b ∈ Fin y ] (a +ꟳ b ≡ y)
  inv = ?∥_| : Tree → ℕ
| leaf | = 1
| fork t1 t2 | = | t1 | + | t2 |


  Tree : {x : ℕ} → (y : Fin x) → Type
  TreeSplit : {x : ℕ} → (a : Fin x) → Tree a → Tree (inv x a)
  Tree zero = ⊤
  Tree (suc n) = Σ (Fin n) {!!}


  -- data Tree : Type where
  --   Leaf : Tree
  --   Fork : Tree → Tree → Tree
-- -}
-- -}
-- -}
-- -}
