<!--
```
module Dissertation.Tree where

open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary.Base
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.Fin.Minus
open import VSet.Data.Fin.SumSplit
  using (⊎≅+; ⊎→+; +→⊎) renaming (sect to ⊎+sect; retr to ⊎+retr)
open import VSet.Data.InjFun.Equality
open import VSet.Data.InjFun.Injection
open import VSet.Data.InjFun.Properties
open import VSet.Data.Nat
open import VSet.Data.Nat hiding (_+_; ¬-<-zero)
open import VSet.Data.Nat hiding (¬-<-zero)
open import VSet.Data.Nat using (ℕ; zero; suc; _+_)
open import VSet.Data.Nat.WellFounded
open import VSet.Data.Sum.Properties
open import VSet.Data.SumTree.Base hiding (α; α⁻¹)
open import VSet.Data.SumTree.Metrics
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Path
open import VSet.Prelude
open import VSet.Relation.WellFounded.Base
open import VSet.Relation.WellFounded.Lex
```
-->

\begin{verbatim}[hide]
module DissertationTex.Tree where

open import Cubical.Core.Primitives
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Binary.Base
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.Fin.Minus
open import VSet.Data.Fin.SumSplit
  using (⊎≅+; ⊎→+; +→⊎) renaming (sect to ⊎+sect; retr to ⊎+retr)
open import VSet.Data.InjFun.Equality
open import VSet.Data.InjFun.Injection
open import VSet.Data.InjFun.Properties
open import VSet.Data.Nat
open import VSet.Data.Nat hiding (_+_; ¬-<-zero)
open import VSet.Data.Nat hiding (¬-<-zero)
open import VSet.Data.Nat using (ℕ; zero; suc; _+_)
open import VSet.Data.Nat.WellFounded
open import VSet.Data.Sum.Properties
open import VSet.Data.SumTree.Base hiding (α; α⁻¹)
open import VSet.Data.SumTree.Metrics
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Path
open import VSet.Prelude
open import VSet.Relation.WellFounded.Base
open import VSet.Relation.WellFounded.Lex
\end{verbatim}


```
flatten : (A : Tree ℕ) → ⟦ A ⟧ₛ → ⟦ Σ∥ A ∥ ⟧
flatten ⟨ X ⟩ₜ a = a
flatten (A & B) (inl x) = ⊎→+ Σ∥ A ∥ Σ∥ B ∥ (inl (flatten A x))
flatten (A & B) (inr y) = ⊎→+ Σ∥ A ∥ Σ∥ B ∥ (inr (flatten B y))
```

```
unflatten : (A : Tree ℕ) → ⟦ Σ∥ A ∥ ⟧ → ⟦ A ⟧ₛ
unflatten ⟨ X ⟩ₜ a = a
unflatten (A & B) a with +→⊎ Σ∥ A ∥ Σ∥ B ∥ a
... | inl x = inl (unflatten A x)
... | inr y = inr (unflatten B y)
```

```
drop-0-base : (A : Tree ℕ) → Tree ℕ
drop-0-base ⟨ X ⟩ₜ = ⟨ X ⟩ₜ
drop-0-base (A & B) with Σ∥ A ∥ | Σ∥ B ∥
... | zero | bn = drop-0-base B
... | suc an | zero = drop-0-base A
... | suc an | suc bn = drop-0-base A & drop-0-base B
```

```
open WFI

0L-R : (A B : Tree ℕ) → Σ∥ A ∥ ≡ 0 →  0L∥ A & B ∥ ≡ suc 0L∥ B ∥
0L-R A B ΣA≡0 =
  0L∥ A & B ∥
    ≡⟨ refl ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
    ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥ )) ΣA≡0 ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) 0
    ≡⟨ refl ⟩
  suc 0L∥ B ∥ ▯
```

```
0B<0LA+B : (A B : Tree ℕ) → Σ∥ A ∥ ≡ 0 → 0L∥ B ∥ < 0L∥ A & B ∥
0B<0LA+B A B ΣA≡0 = subst (0L∥ B ∥ <_) (sym (0L-R A B ΣA≡0)) ≤-refl
```

```
Σ≢0→Σ≥1 : (A : Tree ℕ) (ΣA≢0 : Σ∥ A ∥ ≢ 0) → Σ ℕ (λ k → k +ℕ 1 ≡ Σ∥ A ∥)
Σ≢0→Σ≥1 A ΣA≢0 = ≢0→≥1 Σ∥ A ∥ ΣA≢0
```

```
0A+B≡0A' : (A B : Tree ℕ) → Σ∥ A ∥ ≥ 1 → 0L∥ A & B ∥ ≡ suc 0L∥ A ∥
0A+B≡0A' A B ΣA≥1 =
  0L∥ A & B ∥
    ≡⟨ refl ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) Σ∥ A ∥
    ≡⟨ cong (forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥)) (
        sym (snd (ΣA≥1)) ∙ +-comm (fst (ΣA≥1)) 1) ⟩
  forkℕ (suc 0L∥ B ∥) (suc 0L∥ A ∥) (suc (fst ΣA≥1))
    ≡⟨ refl ⟩
  suc 0L∥ A ∥ ▯
```

```
0A<0A+B : (A B : Tree ℕ) → Σ∥ A ∥ ≥ 1 → 0L∥ A ∥ < 0L∥ A & B ∥
0A<0A+B A B ΣA≥1 = subst (0L∥ A ∥ <_) (sym (0A+B≡0A' A B ΣA≥1)) ≤-refl
```

```
≡suc→≥1 : {x y : ℕ} → x ≡ suc y → x ≥ 1
≡suc→≥1 {x} {y} x≡sy = y , +-comm y 1 ∙ sym x≡sy
```

```
Σ≡0→Empty : (A : Tree ℕ) → (Σ∥ A ∥ ≡ 0) → ¬ ⟦ A ⟧ₛ
Σ≡0→Empty ⟨ X ⟩ₜ Σ≡0 a = equivFun Fin0≃⊥ (transport {A = ⟦ ⟨ X ⟩ₜ ⟧ₛ} eq' a)
  where
    eq' : ⟦ ⟨ X ⟩ₜ ⟧ₛ ≡ Fin 0
    eq' =
      ⟦ ⟨ X ⟩ₜ ⟧ₛ
        ≡⟨ refl ⟩
      [_]ₛ (map ⟦_⟧ ⟨ X ⟩ₜ)
        ≡⟨ refl ⟩
      [_]ₛ (fold (λ Y → ⟨ ⟦ Y ⟧ ⟩ₜ) _&_ ⟨ X ⟩ₜ)
        ≡⟨ refl ⟩
      [_]ₛ ⟨ ⟦ X ⟧ ⟩ₜ
        ≡⟨ refl ⟩
      ⟦ X ⟧
        ≡⟨ refl ⟩
      Fin X
        ≡⟨ cong Fin Σ≡0 ⟩
      Fin 0 ▯
Σ≡0→Empty (A & B) Σ≡0 (inl a) = Σ≡0→Empty A (≤0→≡0 ΣA≤0) a
  where ΣA≤0 : Σ∥ A ∥ ≤ 0
        ΣA≤0 = Σ∥ B ∥ , +-comm Σ∥ B ∥ Σ∥ A ∥ ∙ Σ≡0
Σ≡0→Empty (A & B) Σ≡0 (inr a) = Σ≡0→Empty B (≤0→≡0 ΣB≤0) a
  where ΣB≤0 : Σ∥ B ∥ ≤ 0
        ΣB≤0 = Σ∥ A ∥ , Σ≡0
```

```
deflate-rec
  : (A : Tree ℕ) → Acc _≺₀ₗ_ A
  → Tree ℕ
deflate-&-rec
  : (A B : Tree ℕ) → Singleton Σ∥ A ∥ → Acc _≺₀ₗ_ (A & B)
  → Tree ℕ
```

```
deflate-&-rec A B (zero , ΣA≡0) (acc rs) =
  deflate-rec B (rs B (0B<0LA+B A B ΣA≡0))
deflate-&-rec A B (suc _ , ΣA≡s) (acc rs) = 
  let
    accA = rs A (0A<0A+B A B (≡suc→≥1 ΣA≡s))
    C = deflate-rec A accA
  in C & B
```

```
deflate-rec ⟨ zero ⟩ₜ _ = ⟨ zero ⟩ₜ
deflate-rec ⟨ suc X ⟩ₜ _ = ⟨ suc X ⟩ₜ
deflate-rec (A & B) (acc r) = deflate-&-rec A B (inspect' Σ∥ A ∥) (acc r)
```

```
deflate : Tree ℕ → Tree ℕ
deflate A = deflate-rec A (≺₀ₗ-wellFounded A)
```

```
deflateIndependentOfWf : (A : Tree ℕ) → (acc1 acc2 : Acc _≺₀ₗ_ A) →
  deflate-rec A acc1 ≡ deflate-rec A acc2
deflateIndependentOfWf ⟨ zero ⟩ₜ acc1 acc2 = refl
deflateIndependentOfWf ⟨ suc X ⟩ₜ acc1 acc2 = refl
deflateIndependentOfWf (A & B) (acc r1) (acc r2) with inspect' Σ∥ A ∥
... | zero , ΣA≡0 =
  deflate-&-rec A B (zero , ΣA≡0) (acc r1)
    ≡⟨ refl ⟩
  (deflate-rec B (r1 B 0L-dec))
    ≡⟨ deflateIndependentOfWf B (r1 B 0L-dec)
                                (r2 B 0L-dec) ⟩
  (deflate-rec B (r2 B 0L-dec))
    ≡⟨ refl ⟩
  (deflate-&-rec A B (zero , ΣA≡0) (acc r2)) ▯
  where 0L-dec : 0L∥ B ∥ < 0L∥ A & B ∥ 
        0L-dec = 0B<0LA+B A B ΣA≡0
... | suc ΣA , ΣA≢0 =
  (deflate-&-rec A B (suc ΣA , ΣA≢0) (acc r1))
    ≡⟨ refl ⟩
  (deflate-rec A (r1 A 0L-dec)) & B
    ≡⟨ cong (_& B) $ deflateIndependentOfWf
      A (r1 A 0L-dec) (r2 A 0L-dec) ⟩
  (deflate-rec A (r2 A 0L-dec)) & B
    ≡⟨ refl ⟩
  (deflate-&-rec A B (suc ΣA , ΣA≢0) (acc r2)) ▯
  where 0L-dec : 0L∥ A ∥ < 0L∥ A & B ∥
        0L-dec = 0A<0A+B A B (≡suc→≥1 ΣA≢0)
```

