<!--
```
module Dissertation.Splice where

open import Cubical.Data.Maybe
open import Cubical.Data.Nat
  using (ℕ; _+_; +-zero; +-suc; zero; suc;
        +-assoc; +-comm)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Minus
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
  using (fzero≡subst-fzero;
         subst-fsuc-reorder;
         finject-fsuc-reorder;
         finject0≡subst;
         ≉fsuc )
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

\begin{verbatim}[hide]
module DissertationTex.Splice where

open import Cubical.Data.Maybe
open import Cubical.Data.Nat
  using (ℕ; _+_; +-zero; +-suc; zero; suc;
        +-assoc; +-comm)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Minus
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
  using (fzero≡subst-fzero;
         subst-fsuc-reorder;
         finject-fsuc-reorder;
         finject0≡subst;
         ≉fsuc)
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
\end{verbatim}

```
fsplice : ∀ {x} → Fin (suc x) → Fin x → Fin (suc x)
fsplice fzero a = fsuc a
fsplice (fsuc b) fzero = fzero
fsplice (fsuc b) (fsuc a) = fsuc (fsplice b a)
```

```
-- Alternate definition.
fsplice'-cases : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x) → (Bichotomyᶠ b a)
               → Fin (suc x)
fsplice'-cases _ a (fle _) = fsuc a
fsplice'-cases _ a (fgt _) = finj a
```

```
fsplice'-cases-eq
   : ∀ {x} → {b : Fin (suc x)} → {a : Fin x}
   → (u v : Bichotomyᶠ b a)
   → fsplice'-cases b a u ≡ fsplice'-cases b a v
fsplice'-cases-eq (fle u) (fle v) = refl
fsplice'-cases-eq (fle u) (fgt v) = absurd (≤ᶠ→≯ᶠ u v)
fsplice'-cases-eq (fgt u) (fle v) = absurd (≤ᶠ→≯ᶠ v u)
fsplice'-cases-eq (fgt u) (fgt v) = refl
```

```
fsplice' : ∀ {x : ℕ} → Fin (suc x) → Fin x → Fin (suc x)
fsplice' b a = fsplice'-cases b a (b ≤?ᶠ a)
```

```
fsplice≡fsplice'
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x)
  → fsplice b a ≡ fsplice' b a
fsplice≡fsplice' fzero fzero = refl
fsplice≡fsplice' fzero (fsuc a) = refl
fsplice≡fsplice' (fsuc b) fzero = refl
fsplice≡fsplice' (fsuc b) (fsuc a) with (fsuc b ≤?ᶠ fsuc a)
... | fle b'≤a' = 
  fsuc (fsplice b a)
    ≡⟨ cong fsuc (fsplice≡fsplice' b a) ⟩
  fsuc (fsplice' b a)
    ≡⟨ refl ⟩
  fsuc (fsplice'-cases b a (b ≤?ᶠ a))
    ≡⟨ cong fsuc (fsplice'-cases-eq (b ≤?ᶠ a) (fle (≤-pred b'≤a'))) ⟩
  fsuc (fsplice'-cases b a (fle (≤-pred b'≤a')))
    ≡⟨ refl ⟩
  fsuc (fsuc a)
    ≡⟨ refl ⟩
  fsplice'-cases (fsuc b) (fsuc a) (fle b'≤a') ▯
... | fgt (<fsuc b>a) =
  fsuc (fsplice b a)
    ≡⟨ cong fsuc (fsplice≡fsplice' b a) ⟩
  fsuc (fsplice' b a)
    ≡⟨ refl ⟩
  fsuc (fsplice'-cases b a (b ≤?ᶠ a))
    ≡⟨ cong fsuc (fsplice'-cases-eq (b ≤?ᶠ a) (fgt b>a)) ⟩
  fsuc (fsplice'-cases b a (fgt b>a))
    ≡⟨ refl ⟩
  fsuc (finj a)
    ≡⟨ refl ⟩
  fsplice'-cases (fsuc b) (fsuc a) (fgt (<fsuc b>a)) ▯
```

```
fcross : ∀ {x : ℕ} → (b : Fin x) → (a : Fin (suc x)) → Fin x
fcross fzero fzero = fzero
fcross (fsuc b) fzero = fzero
fcross fzero (fsuc a) = a
fcross (fsuc b) (fsuc a) = fsuc (fcross b a)
```

```
fcross₂ : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
            → Fin (suc x)
fcross₂ _ fzero = fzero
fcross₂ fzero (fsuc a) = a
fcross₂ {suc x} (fsuc b) (fsuc a) =
  fsuc (fcross₂ b a)
```

```
fcross'-cases
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
  → Bichotomyᶠ a b
  → Fin (suc x)
fcross'-cases b a (fle a≤b) = fin-restrict-≤ a a≤b
fcross'-cases b a (fgt a>b) = pred a
```

```
fcross' : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
        → Fin (suc x)
fcross' b a = fcross'-cases b a (a ≤?ᶠ b)
```

```
fjoin-cases : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
                → Trichotomyᶠ a b → Fin x
fjoin-cases b a a≉b (flt a<b) = fin-restrict-< a a<b
fjoin-cases b a a≉b (feq a≈b) = absurd (a≉b a≈b)
fjoin-cases b (fsuc a) a≉b (fgt b<a) = a
```

```
fjoin : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
           → Fin x
fjoin b a a≉b = fjoin-cases b a a≉b (a ≟ᶠ b)
```

```
-- Another alternate definition
fjoinMaybe
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc x))
  → Maybe (Fin x)
fjoinMaybe fzero fzero = nothing
fjoinMaybe {suc x} fzero (fsuc a) = just a
fjoinMaybe {suc x} (fsuc b) fzero = just fzero
fjoinMaybe {suc x} (fsuc b) (fsuc a) =
  map-Maybe fsuc (fjoinMaybe b a)
```

```
-- Another alternate definition
fjoinMaybe'
  : ∀ {x : ℕ} → (b : Fin (suc (suc x))) → (a : Fin (suc (suc x)))
  → Maybe (Fin (suc x))
fjoinMaybe' b a with a ≟ᶠ b
... | flt a<b = just (fin-restrict-< a a<b)
... | feq a≡b = nothing
... | fgt b<a = just (pred a)
```

```
fcross≡fcross'
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin (suc (suc x)))
  → fcross b a ≡ fcross' b a
fcross≡fcross' fzero fzero = refl
fcross≡fcross' fzero (fsuc a) = refl
fcross≡fcross' (fsuc b) fzero = refl
fcross≡fcross' {x = suc x} (fsuc b) (fsuc a) with a ≤?ᶠ b 
... | fle a≤b =
  fcross (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (fcross b a)
    ≡⟨ cong fsuc (fcross≡fcross' b a) ⟩
  fsuc (fcross'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ fcross'-cases b a) (isPropBichotomyᶠ (a ≤?ᶠ b) (fle a≤b)) ⟩
  fsuc (fcross'-cases b a (fle a≤b))
    ≡⟨ refl ⟩
  fsuc (fin-restrict-≤ a a≤b)
    ≡⟨ refl ⟩
  fsuc (fin-restrict-< a (≤ᶠ→<ᶠ a≤b))
    ≡⟨ cong (fin-restrict-< (fsuc a)) (sym (fsuc≤fsuc→<fsuc a≤b) ) ⟩
  fin-restrict-< (fsuc a) (≤ᶠ→<ᶠ (fsuc≤fsuc a≤b))
    ≡⟨ refl ⟩
  fin-restrict-≤ (fsuc a) (fsuc≤fsuc a≤b)
    ≡⟨ refl ⟩
  fcross'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fle a≤b))
    ≡⟨ cong (fcross'-cases (fsuc b) (fsuc a))
            (isPropBichotomyᶠ (≤?ᶠ-suc (fle a≤b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  fcross'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
... | fgt a>b =
  fcross (fsuc b) (fsuc a)
    ≡⟨ refl ⟩
  fsuc (fcross b a)
    ≡⟨ cong fsuc (fcross≡fcross' b a) ⟩
  fsuc (fcross'-cases b a (a ≤?ᶠ b))
    ≡⟨ cong (fsuc ∘ fcross'-cases b a) (isPropBichotomyᶠ (a ≤?ᶠ b) (fgt a>b)) ⟩
  fsuc (fcross'-cases b a (fgt a>b))
    ≡⟨ refl ⟩
  fsuc (pred a)
    ≡⟨ fsuc∘pred≡id {y = 1} (≉fsym (<ᶠ→≉ (≤<ᶠ-trans (fzero≤a b) a>b))) ⟩
  a
    ≡⟨ refl ⟩
  fcross'-cases (fsuc b) (fsuc a) (≤?ᶠ-suc (fgt a>b))
    ≡⟨ cong (fcross'-cases (fsuc b) (fsuc a))
            (isPropBichotomyᶠ (≤?ᶠ-suc (fgt a>b)) (fsuc a ≤?ᶠ fsuc b)) ⟩
  fcross'-cases (fsuc b) (fsuc a) (fsuc a ≤?ᶠ fsuc b) ▯
open Iso
```

```
⊎→+ : ∀ (X Y : ℕ) → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ X + Y ⟧
⊎→+ X Y (inl a) = finject Y a
⊎→+ X Y (inr a) = fshift X a
```

```
inc : ∀ (X Y : ℕ) → ⟦ X ⟧ ⊎ ⟦ Y ⟧ → ⟦ suc X ⟧ ⊎ ⟦ Y ⟧
inc X Y (inl a) = inl (fsuc a)
inc X Y (inr a) = inr a
```

```
+→⊎ : ∀ (X Y : ℕ) → ⟦ X + Y ⟧ → ⟦ X ⟧ ⊎ ⟦ Y ⟧
+→⊎ zero Y a = inr a
+→⊎ (suc X) Y fzero = inl fzero
+→⊎ (suc X) Y (fsuc a) = inc X Y (+→⊎ X Y a)
```

```
+→⊎-X-0≡inl : (X : ℕ) (a : ⟦ X + 0 ⟧)
            → +→⊎ X 0 a ≡ inl (subst Fin (+-zero X) a)
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
```

```
⊎→+-inc : ∀ (X Y : ℕ) (z : ⟦ X ⟧ ⊎ ⟦ Y ⟧)
        → ⊎→+ (suc X) Y (inc X Y z) ≡ fsuc (⊎→+ X Y z)
⊎→+-inc X Y (inl a) = finject-fsuc-reorder a
⊎→+-inc X Y (inr a) = refl
```

```
sect : ∀ (X Y : ℕ) → section {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} (⊎→+ X Y) (+→⊎ X Y)
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

```
retr : ∀ (X Y : ℕ) → retract {A = ⟦ X ⟧ ⊎ ⟦ Y ⟧} (⊎→+ X Y) (+→⊎ X Y)
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
```

```
⊎↔+ : ∀ (X Y : ℕ) → Iso (⟦ X ⟧ ⊎ ⟦ Y ⟧) ⟦ X + Y ⟧
⊎↔+ X Y = iso (⊎→+ X Y) (+→⊎ X Y) (sect X Y) (retr X Y)
```

```
fsplice≉b : ∀ {x} → (b : Fin (suc x)) → (a : Fin x) → fsplice b a ≉ᶠ b
fsplice≉b fzero a = fsuc≉fzero
fsplice≉b (fsuc b) fzero = fzero≉fsuc
fsplice≉b (fsuc b) (fsuc a) ne = 
  let rec≉b = fsplice≉b b a
  in rec≉b (≈fsuc-injective ne)
```

```
fsuc-fjoin 
  : ∀ {x : ℕ} → (b a : Fin (suc x)) → (a≉b : a ≉ᶠ b)
  → fjoin (fsuc b) (fsuc a) (≉fsuc a≉b)
  ≡ fsuc (fjoin b a a≉b)
fsuc-fjoin b        a a≉b with (a ≟ᶠ b)
fsuc-fjoin b        a a≉b | flt a<b = refl
fsuc-fjoin b        a a≉b | feq a≈b = absurd (a≉b a≈b)
fsuc-fjoin b (fsuc a) a≉b | fgt a>b = refl
```

```
fjoin-irrelevant
  : ∀ {x : ℕ} → (b a : Fin (suc x))
  → (u v : a ≉ᶠ b)
  → fjoin b a u ≡ fjoin b a v
fjoin-irrelevant b        a u v with (a ≟ᶠ b)
fjoin-irrelevant b        a u v | flt a<b = refl
fjoin-irrelevant b        a u v | feq a≈b = absurd (u a≈b)
fjoin-irrelevant b (fsuc a) u v | fgt a>b = refl
```

```
fjoin-cong
  : ∀ {x} → {b1 b2 a1 a2 : Fin (suc x)}
  → (p : b1 ≡ b2) → (q : a1 ≡ a2)
  → (ne : a1 ≉ᶠ b1)
  → fjoin b1 a1 ne ≡ fjoin b2 a2 (subst2 _≉ᶠ_ q p ne)
fjoin-cong {b1 = b1} {b2} {a1} {a2} p q ne i =
  fjoin (p i) (q i) (subst2-filler _≉ᶠ_ q p ne i)
```

```
-- This could be simplified.
fjoin-fsplice-inverse
  : ∀ {x : ℕ} → (b : Fin (suc x)) → (a : Fin x)
  → (fsplicea≉b : fsplice b a ≉ᶠ b)
  → fjoin b (fsplice b a) fsplicea≉b ≡ a
fjoin-fsplice-inverse {zero} fzero ()
fjoin-fsplice-inverse {suc zero} fzero fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} fzero fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} fzero (fsuc a) fsplicea≉b = refl
fjoin-fsplice-inverse {suc zero} (fsuc b) fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} (fsuc b) fzero fsplicea≉b = refl
fjoin-fsplice-inverse {suc (suc x)} (fsuc b) (fsuc a) fsplicea'≉b' =
  fjoin (fsuc b) (fsplice (fsuc b) (fsuc a)) fsplicea'≉b'  
    ≡⟨ refl ⟩
  fjoin (fsuc b) (fsuc (fsplice b a)) fsplicea'≉b'  
    ≡⟨ fjoin-irrelevant (fsuc b) (fsuc (fsplice b a))
       fsplicea'≉b' (≉fsuc (fsplice≉b b a)) ⟩
  fjoin (fsuc b) (fsuc (fsplice b a)) 
   (≉fsuc (fsplice≉b b a))
    ≡⟨ fsuc-fjoin b (fsplice b a) (fsplice≉b b a) ⟩
  fsuc (fjoin b (fsplice b a)
                  (fsplice≉b b a))
    ≡⟨ cong fsuc (fjoin-irrelevant b (fsplice b a)
        (fsplice≉b b a)
        (λ a≈b → fsplice≉b (fsuc b) (fsuc a) (≈fsuc a≈b))) ⟩
  fsuc (fjoin b (fsplice b a) 
                  (λ a≈b → fsplice≉b (fsuc b) (fsuc a) (≈fsuc a≈b)))
    ≡⟨ refl ⟩
  fsuc (fjoin b (fsplice b a) 
   (fsplice≉b b a))
    ≡⟨ cong fsuc (fjoin-fsplice-inverse b a (fsplice≉b b a)) ⟩
  fsuc a ▯
```

```
fsplice-isInjective
  : ∀ {m} {a : Fin (suc m)} {b c : Fin m}
  → fsplice a b ≡ fsplice a c → b ≡ c
fsplice-isInjective {a = a} {fzero} {fzero} fsplice-eq = refl
fsplice-isInjective {a = fzero} {b} {c} fsplice-eq = fsuc-injective fsplice-eq
fsplice-isInjective {a = fsuc a} {fzero} {fsuc c} fsplice-eq =
  absurd (fzero≢fsuc fsplice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fzero} fsplice-eq =
  absurd (fsuc≢fzero fsplice-eq)
fsplice-isInjective {a = fsuc a} {fsuc b} {fsuc c} fsplice-eq =
  cong fsuc $ fsplice-isInjective (fsuc-injective fsplice-eq)
```

```
≤→fsplice≈suc : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
              → a2 ≤ᶠ finj a1 → fsplice a2 a1 ≈ᶠ fsuc a1
≤→fsplice≈suc fzero fzero a2≤a1 = ≈fsuc ≈fzero
≤→fsplice≈suc fzero (fsuc a2) (inr a2'≈0) = absurd (fsuc≉fzero a2'≈0)
≤→fsplice≈suc (fsuc a1) fzero a2≤a1 = {!!}
≤→fsplice≈suc {suc m} (fsuc a1) (fsuc a2) rec-le =
  ≈fsuc (≤→fsplice≈suc a1 a2 (≤ᶠ-respects-pred rec-le))
```

```
>→fsplice≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → finj a1 <ᶠ a2 → fsplice a2 a1 ≈ᶠ finj a1
>→fsplice≈id fzero (fsuc a2) a1<a2 = ≈refl
>→fsplice≈id {suc m} (fsuc a1) (fsuc a2) a1<a2 =
  ≈fsuc (>→fsplice≈id a1 a2 (<ᶠ-respects-pred a1<a2))
```

```
<→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 <ᶠ a1 → fcross a1 a2 ≈ᶠ a2
<→fcross≈id (fsuc a1) fzero a2<a1 = ≈fzero
<→fcross≈id {suc m} (fsuc a1) (fsuc a2) (<fsuc a2<a1) =
  ≈fsuc (<→fcross≈id a1 a2 a2<a1)
```

```
≈→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≈ᶠ a1 → fcross a1 a2 ≈ᶠ a2
≈→fcross≈id fzero fzero _ = ≈fzero
≈→fcross≈id (fsuc a1) fzero _ = ≈fzero
≈→fcross≈id fzero (fsuc a2) a2'≈0 = absurd (fsuc≉fzero a2'≈0)
≈→fcross≈id {suc m} (fsuc a1) (fsuc a2) a2≈a1 =
  ≈fsuc (≈→fcross≈id a1 a2 (≈fsuc-injective a2≈a1))
```

```
≤→fcross≈id : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                → a2 ≤ᶠ a1 → fcross a1 a2 ≈ᶠ a2
≤→fcross≈id a1 a2 (inl a2<a1) = <→fcross≈id a1 a2 a2<a1
≤→fcross≈id a1 a2 (inr a2≈a1) = ≈→fcross≈id a1 a2 a2≈a1
```

```
>→fcross≈pred : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                  → finj a1 <ᶠ a2 → fcross a1 a2 ≈ᶠ pred a2
>→fcross≈pred fzero (fsuc a2) a2>a1 = ≈refl
>→fcross≈pred {suc m} (fsuc a1) (fsuc (fsuc a2)) (<fsuc a2>a1) =
  ≈fsuc (>→fcross≈pred a1 (fsuc a2) a2>a1)
```

```
fsplice≈case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
             → fsplice a2 a1 ≈ᶠ(case≤?ᶠ a2 (finj a1) (fsuc a1) (finj a1))
fsplice≈case a1 a2 with (a2 ≤?ᶠ finj a1)
... | fle a2≤a1 = ≤→fsplice≈suc a1 a2 a2≤a1
... | fgt a2>a1 = >→fsplice≈id a1 a2 a2>a1
```

```
-- fcross≈case : ∀ {m} → (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
--                 → fcross a1 a2
--                 ≈ᶠ case≤?ᶠ a2 (finj a1) a2 (finj (pred a2))
-- fcross≈case a1 a2 with (a2 ≤?ᶠ a1)
-- ... | fle a2≤a1 = ≤→fcross≈id a1 a2 a2≤a1
-- ... | fgt a2>a1 = cong finj (>→fcross≈pred a1 a2 a2>a1)
```

```
finj∘fsuc≈fsuc∘finj : ∀ {x} (a : Fin (suc x)) → finj (fsuc a) ≈ᶠ fsuc (finj a)
finj∘fsuc≈fsuc∘finj a = ≈refl
```

```
fsplice-fsplice-fcross 
  : ∀ {m} →  (b : Fin (suc (suc m))) → (c : Fin (suc m))
  → fsplice (fsplice b c) (fcross c b)
  ≡ b
fsplice-fsplice-fcross fzero fzero = refl
fsplice-fsplice-fcross fzero (fsuc c) = refl
fsplice-fsplice-fcross (fsuc b) fzero = refl
fsplice-fsplice-fcross {m = suc m} (fsuc b) (fsuc c) =
  fsplice (fsplice (fsuc b) (fsuc c))
          (fcross (fsuc c) (fsuc b))
    ≡⟨ refl ⟩
  fsplice (fsuc (fsplice b c))
          (fsuc (fcross c b))
    ≡⟨ refl ⟩
  fsuc (fsplice (fsplice b c)
                (fcross c b))
    ≡⟨ cong fsuc (fsplice-fsplice-fcross b c) ⟩
  fsuc b ▯
```

```
fjoin-fsplice-fsplice-fcross-fsplice
  : ∀ {n} → (b : Fin (suc (suc n)))
  → (c : Fin (suc n))
  → (ne : fsplice b c ≉ᶠ fsplice (fsplice b c) (fcross c b))
  → fjoin (fsplice (fsplice b c) (fcross c b)) (fsplice b c) ne
  ≡ fjoin b (fsplice b c)
              (subst (fsplice b c ≉ᶠ_)
                     (fsplice-fsplice-fcross b c) ne)
fjoin-fsplice-fsplice-fcross-fsplice b c ne i
  = fjoin (fsplice-fsplice-fcross b c i) (fsplice b c)
              (subst-filler (fsplice b c ≉ᶠ_) (fsplice-fsplice-fcross b c) ne i)
```

```
fin-restrict-<-a≈a
  : ∀ {x} {b : Fin (suc x)} (a : Fin y)
  → (a<b : a <ᶠ b) → fin-restrict-< a a<b ≈ᶠ a
fin-restrict-<-a≈a {x = suc x} fzero <fzero = ≈fzero
fin-restrict-<-a≈a {x = suc x} (fsuc a) (<fsuc a<b) =
  ≈fsuc (fin-restrict-<-a≈a a a<b)
```

```
fjoin-fsplice'
  : ∀ {n} → (b : Fin (suc n))
  → (c : Fin (suc (suc n))) 
  → (ne : c ≉ᶠ fsplice' c b)
  → (fjoin (fsplice' c b) c ne)
  ≡ fcross' b c
fjoin-fsplice' b c ne with c ≤?ᶠ b
fjoin-fsplice' b c ne | fle c≤b =
  fjoin (fsplice'-cases c b (fle c≤b)) c ne
    ≡⟨ refl ⟩
  fjoin-cases (fsuc b) c ne (c ≟ᶠ fsuc b)
    ≡⟨ cong (fjoin-cases (fsuc b) c ne)
            (isPropTrichotomyᶠ (c ≟ᶠ fsuc b) (flt (≤ᶠ→<ᶠ c≤b))) ⟩
  fjoin-cases (fsuc b) c ne (flt (≤ᶠ→<ᶠ c≤b))
    ≡⟨ refl ⟩
  fin-restrict-< c (≤ᶠ→<ᶠ c≤b)
    ≡⟨ refl ⟩
  fin-restrict-≤ c c≤b
    ≡⟨ refl ⟩
  fcross'-cases b c (fle c≤b) ▯
fjoin-fsplice' b (fsuc c) ne | fgt c>b =
  fjoin-cases (fsplice'-cases (fsuc c) b (fgt c>b)) (fsuc c) ne
                  (fsuc c ≟ᶠ fsplice'-cases (fsuc c) b (fgt c>b))
    ≡⟨ refl ⟩
  fjoin-cases (finj b) (fsuc c) ne (fsuc c ≟ᶠ finj b)
    ≡⟨ cong (fjoin-cases (finj b) (fsuc c) ne)
              (isPropTrichotomyᶠ (fsuc c ≟ᶠ finj b) (fgt (<ᶠ-inj-l c>b))) ⟩
  fjoin-cases (finj b) (fsuc c) ne (fgt (<ᶠ-inj-l c>b))
    ≡⟨ refl ⟩
  c
    ≡⟨ refl ⟩
  pred (fsuc c)
    ≡⟨ refl ⟩
  fcross'-cases b (fsuc c) (fgt c>b) ▯
```

```
fjoin-fsplice-fsplice-fsplice
  : ∀ {n} → (a : Fin (suc (suc n))) → (b : Fin (suc n))
  → (c : Fin (suc n)) 
  → (ne : fsplice a c ≉ᶠ fsplice (fsplice a c) b)
  → (fjoin (fsplice (fsplice a c) b) (fsplice a c) ne)
  ≡ fcross b (fsplice a c)
fjoin-fsplice-fsplice-fsplice a b c ne =
  fjoin (fsplice (fsplice a c) b) (fsplice a c) ne
    ≡⟨ fjoin-cong (fsplice≡fsplice' (fsplice a c) b) refl ne ⟩
  fjoin (fsplice' (fsplice a c) b) (fsplice a c) _
    ≡⟨ fjoin-fsplice' b (fsplice a c) _ ⟩
  fcross' b (fsplice a c)
    ≡⟨ sym (fcross≡fcross' b (fsplice a c)) ⟩
  fcross b (fsplice a c) ▯
```

```
fsplice-fsplice-fsplice-fcross
  : ∀ {m} → (b : Fin (suc (suc m))) → (a : Fin m) → (c : Fin (suc m)) 
  → fsplice (fsplice b c) (fsplice (fcross c b) a)
  ≡ fsplice b (fsplice c a)
fsplice-fsplice-fsplice-fcross fzero fzero fzero = refl
fsplice-fsplice-fsplice-fcross fzero fzero (fsuc c) = refl
fsplice-fsplice-fsplice-fcross fzero (fsuc a) fzero = refl
fsplice-fsplice-fsplice-fcross fzero (fsuc a) (fsuc c) = refl
fsplice-fsplice-fsplice-fcross (fsuc b) fzero fzero = refl
fsplice-fsplice-fsplice-fcross (fsuc b) fzero (fsuc c) = refl
fsplice-fsplice-fsplice-fcross (fsuc b) (fsuc a) fzero = refl
fsplice-fsplice-fsplice-fcross (fsuc b) (fsuc a) (fsuc c) =
  cong fsuc (fsplice-fsplice-fsplice-fcross b a c)
```

```
fcross0≡0 : ∀ {m} → (a : Fin (suc m))
          → fcross a fzero ≡ fzero
fcross0≡0 fzero = refl
fcross0≡0 (fsuc a) = refl
```

```
fcross0s≡pred : ∀ {m} → (a : Fin (suc m))
              → fcross f0 (fsuc a) ≡ a
fcross0s≡pred a = refl
```

```
fcross-fcross-fsplice
  : ∀ {m} → (b : Fin (suc (suc m))) (c : Fin (suc m))
  → (fcross (fcross c b) (fsplice b c)) ≡ c
fcross-fcross-fsplice fzero fzero = refl
fcross-fcross-fsplice fzero (fsuc c) = refl
fcross-fcross-fsplice (fsuc b) fzero = fcross0≡0 b
fcross-fcross-fsplice {m = suc m} (fsuc b) (fsuc c) =
  cong fsuc (fcross-fcross-fsplice b c)
```

```
finject-+ : ∀ (x y z : ℕ) → (a : Fin x)
          → finject z (finject y a)
          ≡ subst Fin (+-assoc x y z) (finject (y + z) a)
finject-+ (suc x) zero z fzero =
  finject z (finject zero fzero)
    ≡⟨ refl ⟩
  finject z fzero 
    ≡⟨ refl ⟩
  fzero 
    ≡⟨ fzero≡subst-fzero (+-assoc x zero z) ⟩
  subst Fin (+-assoc (suc x) zero z) fzero 
    ≡⟨ refl ⟩
  subst Fin (+-assoc (suc x) zero z) (finject (zero + z) fzero) ▯
finject-+ (suc x) zero z (fsuc a) =
  finject z (finject zero (fsuc a))
    ≡⟨ refl ⟩
  finject z (fsuc (finject zero a))
    ≡⟨ refl ⟩
  fsuc (finject z (finject zero a))
    ≡⟨ cong fsuc (finject-+ x 0 z a) ⟩
  fsuc (subst Fin (+-assoc x zero z) (finject (zero + z) a))
    ≡⟨ sym (subst-fsuc-reorder (+-assoc x zero z) (finject (zero + z) a)) ⟩
  subst Fin (+-assoc (suc x) zero z) (fsuc (finject (zero + z) a))
    ≡⟨ refl ⟩
  subst Fin (+-assoc (suc x) zero z) (finject (zero + z) (fsuc a)) ▯
finject-+ (suc x) (suc y) z fzero =
  finject z (finject (suc y) fzero)
    ≡⟨ refl ⟩
  finject z fzero
    ≡⟨ refl ⟩
  fzero
    ≡⟨ fzero≡subst-fzero (+-assoc x (suc y) z) ⟩
  subst Fin (+-assoc (suc x) (suc y) z) fzero
    ≡⟨ refl ⟩
  subst Fin (+-assoc (suc x) (suc y) z) (finject (suc y + z) fzero) ▯ 
finject-+ (suc x) (suc y) z (fsuc a) =
  finject z (finject (suc y) (fsuc a))
    ≡⟨ refl ⟩
  finject z (fsuc (finject (suc y) a))
    ≡⟨ refl ⟩
  fsuc (finject z (finject (suc y) a))
    ≡⟨ {!refl!} ⟩
  fsuc (subst Fin (+-assoc x (suc y) z) (finject (suc y + z) a))
    ≡⟨ sym (subst-fsuc-reorder (+-assoc x (suc y) z) (finject (suc y + z) a)) ⟩
  subst Fin (+-assoc (suc x) (suc y) z) (fsuc (finject (suc y + z) a))
    ≡⟨ refl ⟩
  subst Fin (+-assoc (suc x) (suc y) z) (finject (suc y + z) (fsuc a)) ▯
```

```
fsplice-fcross-fcross-fsplice
  : {n : ℕ} → (b : Fin (suc (suc n))) (c : Fin (suc n)) (d : Fin n)
  → fsplice (fcross (fsplice c d) b) (fcross d c)
  ≡ (fcross (fsplice (fcross c b) d) (fsplice b c))
fsplice-fcross-fcross-fsplice fzero fzero d = refl
fsplice-fcross-fcross-fsplice fzero (fsuc c) fzero = refl
fsplice-fcross-fcross-fsplice fzero (fsuc c) (fsuc d) = refl
fsplice-fcross-fcross-fsplice (fsuc b) fzero fzero = sym (fcross0≡0 (fsplice b f0))
fsplice-fcross-fcross-fsplice (fsuc b) fzero (fsuc d) = sym (fcross0≡0 (fsplice b (fsuc d)))
fsplice-fcross-fcross-fsplice (fsuc b) (fsuc c) fzero = refl
fsplice-fcross-fcross-fsplice (fsuc b) (fsuc c) (fsuc d) =
  cong fsuc (fsplice-fcross-fcross-fsplice b c d)
```

```
fcross-fcross-fcross-fsplice
  : {n : ℕ} → (b : Fin (suc (suc n))) (c : Fin (suc n)) (d : Fin n)
  → fcross (fcross d c) (fcross (fsplice c d) b)
  ≡ fcross d (fcross c b)
fcross-fcross-fcross-fsplice fzero fzero fzero = refl
fcross-fcross-fcross-fsplice fzero fzero (fsuc d) = refl
fcross-fcross-fcross-fsplice fzero (fsuc c) fzero = fcross0≡0 c
fcross-fcross-fcross-fsplice fzero (fsuc c) (fsuc d) = refl
fcross-fcross-fcross-fsplice (fsuc b) fzero fzero = refl
fcross-fcross-fcross-fsplice (fsuc b) fzero (fsuc d) = refl
fcross-fcross-fcross-fsplice (fsuc b) (fsuc c) fzero = refl
fcross-fcross-fcross-fsplice (fsuc b) (fsuc c) (fsuc d) =
  cong fsuc (fcross-fcross-fcross-fsplice b c d)
```

```
fjoin≡fcross : {n : ℕ} → (a : Fin n) (b : Fin (suc n)) → (b≉a : b ≉ᶠ finj a)
             → fjoin (finj a) b b≉a ≡ fcross a b
fjoin≡fcross fzero fzero 0≉0 = absurd (0≉0 ≈refl)
fjoin≡fcross fzero (fsuc b) b'≉0 =
  fjoin (finj f0) (fsuc b) b'≉0
    ≡⟨ refl ⟩
  fjoin-cases (finj f0) (fsuc b) b'≉0 (fsuc b ≟ᶠ finj f0)
    ≡⟨ refl ⟩
  fjoin-cases (finj f0) (fsuc b) b'≉0 (fgt <fzero)
    ≡⟨ refl ⟩
  b
    ≡⟨ refl ⟩
  fcross f0 (fsuc b) ▯
fjoin≡fcross (fsuc a) fzero b≉a = refl
fjoin≡fcross (fsuc a) (fsuc b) b'≉a' =
  fjoin (finj (fsuc a)) (fsuc b) b'≉a'
    ≡⟨ fjoin-irrelevant (fsuc (finj a)) (fsuc b) b'≉a' (≉fsuc (≉fpred b'≉a')) ⟩
  fjoin (fsuc (finj a)) (fsuc b) (≉fsuc (≉fpred b'≉a'))
    ≡⟨ fsuc-fjoin (finj a) b (≉fpred b'≉a') ⟩
  fsuc (fjoin (finj a) b (≉fpred b'≉a'))
    ≡⟨ cong fsuc (fjoin≡fcross a b (≉fpred b'≉a')) ⟩
  fsuc (fcross a b)
    ≡⟨ refl ⟩
  fcross (fsuc a) (fsuc b) ▯
```

```
fjoin-isInjective : {n : ℕ} → (a b c : Fin (suc n)) → (b≉a : b ≉ᶠ a) → (c≉a : c ≉ᶠ a)
                  → fjoin a b b≉a ≡ fjoin a c c≉a → b ≡ c
fjoin-isInjective fzero fzero c 0≉0 c≉0 q = absurd (0≉0 ≈refl)
fjoin-isInjective fzero (fsuc b) fzero b'≉0 0≉0 q = absurd (0≉0 ≈refl)
fjoin-isInjective {suc n} fzero (fsuc b) (fsuc c) b'≉a c'≉a q =
  cong fsuc p
  where p : b ≡ c
        p = b
              ≡⟨ sym (fjoin≡fcross f0 (fsuc b) b'≉a) ⟩
            fjoin f0 (fsuc b) b'≉a
              ≡⟨ q ⟩
            fjoin f0 (fsuc c) c'≉a
              ≡⟨ fjoin≡fcross f0 (fsuc c) c'≉a ⟩
            c ▯
fjoin-isInjective (fsuc a) fzero fzero 0≉a' _ q = refl
fjoin-isInjective {suc n} (fsuc a) fzero (fsuc c) 0≉a' c'≉a' q
  with (fsuc c) ≟ᶠ (fsuc a)
... | flt (<fsuc c<a) = ≈ᶠ→≡ $ ≈ᶠ-trans ≈fzero $ ≈ᶠ-trans (≡→≈ᶠ q)
                      $ ≈fsuc (fin-restrict-<-a≈a c c<a)
... | feq (≈fsuc c≈a) = absurd (c'≉a' (≈fsuc c≈a))
fjoin-isInjective {suc n} (fsuc a) fzero (fsuc (fsuc c)) 0≉a' c'≉a' q
    | fgt (<fsuc c>a) = absurd (fzero≢fsuc q)
fjoin-isInjective {suc n} (fsuc a) (fsuc b) fzero b'≉a' 0≉a' q
  with (fsuc b) ≟ᶠ (fsuc a)
... | flt (<fsuc b<a) = sym $ ≈ᶠ→≡ $ ≈ᶠ-trans ≈fzero $ ≈ᶠ-trans (≡→≈ᶠ (sym q))
                      $ ≈fsuc (fin-restrict-<-a≈a b b<a)
... | feq (≈fsuc b≈a) = absurd (b'≉a' (≈fsuc b≈a))
fjoin-isInjective {suc n} (fsuc a) (fsuc (fsuc b)) fzero b'≉a' 0≉a' q
    | fgt (<fsuc b>a) = absurd (fzero≢fsuc (sym q))
fjoin-isInjective {n = suc n} (fsuc a) (fsuc b) (fsuc c) b≉a c≉a q =
  cong fsuc (fjoin-isInjective a b c (≉fpred b≉a) (≉fpred c≉a) r)
  where
    r : fjoin a b (≉fpred b≉a) ≡ fjoin a c (≉fpred c≉a)
    r = fsuc-injective (
      fsuc (fjoin a b (≉fpred b≉a))
        ≡⟨ sym (fsuc-fjoin a b (≉fpred b≉a)) ⟩
      fjoin (fsuc a) (fsuc b) (≉fsuc (≉fpred b≉a))
        ≡⟨ fjoin-irrelevant (fsuc a) (fsuc b) (≉fsuc (≉fpred b≉a)) b≉a ⟩
      fjoin (fsuc a) (fsuc b) b≉a
        ≡⟨ q ⟩
      fjoin (fsuc a) (fsuc c) c≉a
        ≡⟨ fjoin-irrelevant (fsuc a) (fsuc c) c≉a (≉fsuc (≉fpred c≉a)) ⟩
      fjoin (fsuc a) (fsuc c) (≉fsuc (≉fpred c≉a))
        ≡⟨ fsuc-fjoin a c (≉fpred c≉a) ⟩
      fsuc (fjoin a c (≉fpred c≉a)) ▯)
```

```
t0 = fsplice f0 f0
   , fsplice f0 f1
   , fsplice f1 f0
   , fsplice f1 f1
_ : t0 ≡ (f1 , f2 , f0 , f2)
_ = refl
```

```
t1 : Fin 2 × Fin 2 × Fin 2 × Fin 2
t1 = fjoin f0 (fsplice f0 f0) (fsplice≉b f0 f0)
   , fjoin f0 (fsplice f0 f1) (fsplice≉b f0 f1)
   , fjoin f1 (fsplice f1 f0) (fsplice≉b f1 f0)
   , fjoin f1 (fsplice f1 f1) (fsplice≉b f1 f1)
_ : t1 ≡ (f0 , f1 , f0 , f1)
_ = refl
```

```
t2 : Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2 × Fin 2
t2 = fcross' f0 f0 -- eq
   , fcross' f0 f1 -- pred
   , fcross' f0 f2 -- pred
   , fcross' f1 f0 -- eq
   , fcross' f1 f1 -- eq
   , fcross' f1 f2 -- pred
_ : t2 ≡ (f0 , f0 , f1 , f0 , f1 , f1)
_ = refl
```
