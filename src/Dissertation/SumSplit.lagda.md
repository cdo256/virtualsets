<!--
```
module Dissertation.SumSplit where

open import Cubical.Data.Maybe
open import Cubical.Data.Nat
  using (ℕ; _+_; +-zero; +-suc; zero; suc;
        +-assoc; +-comm)
open import VSet.Data.Fin.Base hiding (finject; fshift)
open import VSet.Data.Fin.Minus
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
  using (fzero≡subst-fzero;
         subst-fsuc-reorder;
         ≉fsuc)
open import VSet.Data.Inj.Base hiding (apply; inc)
open import VSet.Data.Nat.Order
open import VSet.Data.Nat.Properties
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Prelude

private
  variable
    ℓ : Level
    x y z : ℕ
    a : Fin x
    b : Fin y
```
-->

## Splitting a Finite Set

To define an tensor on a pair of finite functions, the idea is that we
will split the domain, pefrom the injective map separately, and then
join the domains back into a single domain. We define these operations
and show that they are inverses by constructing an isomorphism.

We start with the split function `+→⊎`, which takes a single domain,
and splits it into a left and a right part in such a way that any
value less than `X` will be sorted on the left and any values greater
than or equal to `X` will appear on the right part. We make use of a
helper function `step` which handles the successor case, taking the
output of the recursive call and shifting the left domain up by
1. This gives us one diraction of the bi-conversion.

```
inc : ∀ (X Y : ℕ) → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ suc X ⟧ ⊎ ⟦ Y ⟧
inc X Y (inl a) = inl (fsuc a)
inc X Y (inr a) = inr a

+→⊎ : ∀ (X Y : ℕ) → ⟦ X + Y ⟧ → ⟦ X ⟧ ⊎ ⟦ Y ⟧
+→⊎ zero Y a = inr a
+→⊎ (suc X) Y fzero = inl fzero
+→⊎ (suc X) Y (fsuc a) = inc X Y (+→⊎ X Y a)
```

To write the join operation `⊎→+`, we need to define a pair of
operations on `Fin`: `fshift` and `finject` are complementary
functions that have ranges that don't overlap but do cover the
codomain. We will use this property when defining `⊎≅+`.
```
fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x + y)
fshift zero a = a
fshift (suc x) a = fsuc (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x + y)
finject {suc _} _ fzero = fzero
finject {suc x} y (fsuc a) = fsuc (finject {x} y a)
```

Now the join function, decides based on which side the input came in
from whether to inject (keeping the values the same), or whether to
shift them up by `X`.
```
⊎→+ : ∀ (X Y : ℕ) → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ X + Y ⟧
⊎→+ X Y (inl a) = finject Y a
⊎→+ X Y (inr a) = fshift X a
```

We prove a lemma that if the right domain is empty then splitting will
result in an empty right set (proof ommitted).
```
+→⊎-X-0≡inl : (X : ℕ) (a : ⟦ X + 0 ⟧)
            → +→⊎ X 0 a ≡ inl (subst Fin (+-zero X) a)
```

<!--
```
+→⊎-X-0≡inl (suc X) fzero = cong inl (fzero≡subst-fzero (+-zero X))
+→⊎-X-0≡inl (suc X) (fsuc a) =
  +→⊎ (suc X) 0 (fsuc a)
    ≡⟨ refl ⟩
  inc X 0 (+→⊎ X 0 a)
    ≡⟨ cong (inc X 0) (+→⊎-X-0≡inl X a) ⟩
  inc X 0 (inl (subst Fin (+-zero X) a))
    ≡⟨ refl ⟩
  inl (fsuc (subst Fin (+-zero X) a))
    ≡⟨ cong inl (sym (subst-fsuc-reorder (+-zero X) a)) ⟩
  inl (subst Fin (+-zero (suc X)) (fsuc a)) ▯


finject-fsuc-reorder : ∀ {x y : ℕ} → (a : Fin x)
                      → finject y (fsuc a) ≡ fsuc (finject y a)
finject-fsuc-reorder {suc x} {zero} a = refl
finject-fsuc-reorder {suc x} {suc y} a = refl
finject-fsuc-reorder {zero} {suc y} a = refl

⊎→+-inc : ∀ (X Y : ℕ) (z : ⟦ X ⟧ ⊎ ⟦ Y ⟧)
        → ⊎→+ (suc X) Y (inc X Y z) ≡ fsuc (⊎→+ X Y z)
⊎→+-inc X Y (inl a) = finject-fsuc-reorder a
⊎→+-inc X Y (inr a) = refl
```
-->


<!--
```
finject0≡subst : {x : ℕ} (a : Fin x)
               → finject {x} zero a ≡ subst Fin (sym (+-zero x)) a
finject0≡subst {suc x} fzero =
  resubst (Fin ∘ suc) (λ z → fzero {z}) (sym (+-zero x))
finject0≡subst {suc x} (fsuc a) =
  finject zero (fsuc a) ≡⟨ finject-fsuc-reorder a ⟩
  fsuc (finject zero a) ≡⟨ cong fsuc (finject0≡subst a) ⟩
  fsuc (subst Fin (sym (+-zero x)) a)
    ≡⟨ sym (transport-reorder Fin suc fsuc (sym (+-zero x)) a) ⟩
  subst Fin (sym (+-zero (suc x))) (fsuc a) ▯
```
-->


Now we can define the two cancelation laws, called *section* and
*retraction* in homotpy type theory CITE. These proofs are left out of
this dissertation for space, but they amount to pattern matching and
chaining equivalences. Finally we join these together into an
isomorphism, proving equivalence of the two representations (split and
joined). We can then use these euquivalences to create a tensor
product as we'll see next.
```
sect : ∀ (X Y : ℕ) → section {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} (⊎→+ X Y) (+→⊎ X Y)
retr : ∀ (X Y : ℕ) → retract {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} (⊎→+ X Y) (+→⊎ X Y)

⊎≅+ : ∀ (X Y : ℕ) → Iso (⟦ X ⟧ ⊎ ⟦ Y ⟧) ⟦ X + Y ⟧
⊎≅+ X Y = iso (⊎→+ X Y) (+→⊎ X Y) (sect X Y) (retr X Y)
```

<!--
```
retr zero Y (inr a) = refl
retr (suc X) Y (inl fzero) =
  +→⊎ (suc X) Y (⊎→+ (suc X) Y (inl fzero))
    ≡⟨ refl ⟩
  +→⊎ (suc X) Y (finject Y fzero)
    ≡⟨ refl ⟩
  +→⊎ (suc X) Y fzero
    ≡⟨ refl ⟩
  inl fzero ▯
retr (suc X) zero (inl (fsuc a)) =
  +→⊎ (suc X) zero (⊎→+ (suc X) zero (inl (fsuc a))) ≡⟨ refl ⟩
  +→⊎ (suc X) zero (finject 0 (fsuc a)) ≡⟨ refl ⟩
  +→⊎ (suc X) zero (fsuc (finject 0 a)) ≡⟨ refl ⟩
  inc X zero (+→⊎ X zero (finject 0 a)) ≡⟨ refl ⟩
  inc X zero (+→⊎ X zero (⊎→+ X zero (inl a)))
    ≡⟨ cong (inc X zero) (retr X zero (inl a)) ⟩
  inl (fsuc a) ▯
retr (suc X) (suc Y) (inl (fsuc a)) =
  +→⊎ (suc X) (suc Y) (⊎→+ (suc X) (suc Y) (inl (fsuc a))) ≡⟨ refl ⟩
  +→⊎ (suc X) (suc Y) (finject {x = suc X} (suc Y) (fsuc a)) ≡⟨ refl ⟩
  +→⊎ (suc X) (suc Y) (fsuc (finject {x = X} (suc Y) a)) ≡⟨ refl ⟩
  +→⊎ (suc X) (suc Y) (fsuc (finject {X} (suc Y) a)) ≡⟨ refl ⟩
  inc X (suc Y) (+→⊎ X (suc Y) (finject {X} (suc Y) a)) ≡⟨ refl ⟩
  inc X (suc Y) (+→⊎ X (suc Y) (⊎→+ X (suc Y) (inl a)))
    ≡⟨ cong (inc X (suc Y) ) (retr X (suc Y) (inl a)) ⟩
  inc X (suc Y) (inl a) ≡⟨ refl ⟩
  inl (fsuc a) ▯
retr (suc X) Y (inr a) =
  +→⊎ (suc X) Y (⊎→+ (suc X) Y (inr a)) ≡⟨ refl ⟩
  +→⊎ (suc X) Y (fshift (suc X) a) ≡⟨ refl ⟩
  +→⊎ (suc X) Y (fsuc (fshift X a)) ≡⟨ refl ⟩
  inc X Y (+→⊎ X Y (fshift X a)) ≡⟨ refl ⟩
  inc X Y (+→⊎ X Y (⊎→+ X Y (inr a))) ≡⟨ cong (inc X Y) (retr X Y (inr a)) ⟩
  inc X Y (inr a) ≡⟨ refl ⟩
  inr a ▯
sect zero Y a = refl
sect (suc X) zero fzero = refl
sect (suc X) (suc Y) fzero = refl
sect (suc X) zero (fsuc a) =
  ⊎→+ (suc X) zero (+→⊎ (suc X) zero (fsuc a))
    ≡⟨ cong (⊎→+ (suc X) 0) (+→⊎-X-0≡inl (suc X) (fsuc a)) ⟩
  ⊎→+ (suc X) zero (inl (subst Fin (+-zero (suc X)) (fsuc a)))
    ≡⟨ refl ⟩
  finject zero (subst Fin (+-zero (suc X)) (fsuc a))
    ≡⟨ finject0≡subst ((subst Fin (+-zero (suc X)) (fsuc a))) ⟩
  subst Fin (sym (+-zero (suc X))) (subst Fin (+-zero (suc X)) (fsuc a))
    ≡⟨ subst⁻Subst Fin (+-zero (suc X)) (fsuc a) ⟩
  fsuc a ▯
sect (suc X) (suc Y) (fsuc a) =
  ⊎→+ (suc X) (suc Y) (+→⊎ (suc X) (suc Y) (fsuc a))
    ≡⟨ refl ⟩
  ⊎→+ (suc X) (suc Y) (inc X (suc Y) (+→⊎ X (suc Y) a))
    ≡⟨ ⊎→+-inc X (suc Y) (+→⊎ X (suc Y) a) ⟩
  fsuc (⊎→+ X (suc Y) (+→⊎ X (suc Y) a)) 
    ≡⟨ cong fsuc (sect X (suc Y) a) ⟩
  fsuc a ▯
```
-->

