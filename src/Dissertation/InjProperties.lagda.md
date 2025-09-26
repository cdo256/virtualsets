<!--
```
module Dissertation.InjProperties where

open import Cubical.Data.List.Base hiding ([_])
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Prod.Base hiding (map)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Fin.Splice
open import VSet.Data.Inj.Base hiding (injExt)
open import VSet.Function.Injection
open import VSet.Prelude

private
  variable
    m n : ℕ
```
-->

## Properties of \texttt{\large Inj} {#properties-of-inj}

Next we observe a couple of properties of `Inj`, as defined in section
\ref{definition-of-inj}. 

One key result that we desire is injectivity. We show this by matching
values, and showing that they must be equal. In the first case, they are
both `f0` so the result is immediate. When one value is `f0` and the
other is a successor value, then we use the lemma that fsplice doesn't
map to the pivot. In the final case we use the injectivity of fsplice
and recurse.
```
Inj-isInjective : (f : Inj m n) → is-injective (apply f)
Inj-isInjective f fzero fzero fx≡fy = refl
Inj-isInjective (inc b f) fzero (fsuc y) fx≡fy =
  absurd (fsplice≉b b (apply f y) (≡→≈ᶠ (sym fx≡fy)))
Inj-isInjective (inc b f) (fsuc x) fzero fx≡fy =
  absurd (fsplice≉b b (apply f x) (≡→≈ᶠ fx≡fy))
Inj-isInjective (inc b f) (fsuc x) (fsuc y) fx≡fy =
  cong fsuc (Inj-isInjective f x y (fsplice-isInjective fx≡fy))
```

Another important result is extensionality of `Inj`, which is to say
that `Inj` is entirely determined by its 'graph' (map from domain
elements to codomain). Put another way, no two `Inj` structures act
the same way when applied. This is an important property because it
means to show equality, it's sufficient to prove it element-wise,
which avoids expanding the inductive definition directly. It depends
only on the injectivity of `fsplice` and some basic lemmas in the
cubical library.

```
injExt : ∀ {m n} → (f g : Inj m n)
       → (∀ x → apply f x ≡ apply g x) → f ≡ g
injExt (nul _) (nul _) _ = refl
injExt (inc b f) (inc c g) f'x≡g'x =
  inc b f
    ≡⟨ cong (λ ○ → inc ○ f) (f'x≡g'x f0) ⟩
  inc c f
    ≡⟨ cong (inc c) f≡g ⟩
  inc c g ▯
  where
    fx≡gx : ∀ x → apply f x ≡ apply g x
    fx≡gx x =
      apply f x
        ≡⟨ (fsplice-isInjective
          ((f'x≡g'x (fsuc x))
          ∙ sym (cong (λ ○ → fsplice ○ (apply g x)) (f'x≡g'x f0)))) ⟩
      apply g x ▯
    f≡g : f ≡ g
    f≡g = injExt f g fx≡gx
```

We prove with recursion. The base case is immediate, since
there is only one `nul` function of each size. Now to suppose
`∀ x → apply (inc b f) x ≡ apply (inc c g) x)`. We want to show `b ≡ c` and `f ≡ g`.

(`b ≡ c`): This is immediate from `apply (inc b f) f0 ≡ apply (inc c g) f0`.

(`f ≡ g`): We will do this by using induction by showing
`∀ x → apply f x ≡ apply g x`. This is done by rewriting the assumed
fact in terms of `fsplice`:

  `fsplice b (apply f x) ≡ fsplice c (apply g x)`

then, using the fact `b ≡ c`, we can use the fact that fsplice is
injective, to get, `apply f x ≡ apply g x` as we require. `∎`
