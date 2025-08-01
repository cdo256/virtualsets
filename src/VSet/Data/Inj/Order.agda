module VSet.Data.Inj.Order where

open import VSet.Prelude
open import Cubical.Data.Prod.Base hiding (map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.List.Base hiding ([_])
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base

private
  variable
    m n : ℕ

-- Artificial order for decidability.
-- Lexicographic with deepest inc inserted taking precidence.
data _<ʲ_ : {m n : ℕ} (f g : Inj m n) → Type where
  <j-suc : {m n : ℕ} → {b c : Fin (suc n)} → {f g : Inj m n}
         → f <ʲ g → inc b f <ʲ inc c g 
  <j-fin : {m n : ℕ} → {b c : Fin (suc n)} → {f g : Inj m n}
         → f ≡ g → b <ᶠ c → inc b f <ʲ inc c g 

open _<ʲ_

_≤ʲ_ : {m n : ℕ} (f g : Inj m n) → Type
f ≤ʲ g = (f <ʲ g) ⊎ (f ≡ g)

data Trichotomyʲ {m n : ℕ} (f g : Inj m n) : Type where
  jlt : f <ʲ g → Trichotomyʲ f g
  jeq : f ≡ g → Trichotomyʲ f g
  jgt : g <ʲ f → Trichotomyʲ f g

open Trichotomyʲ

data Bichotomyʲ {m n : ℕ} (f g : Inj m n) : Type where
  jle : f ≤ʲ g → Bichotomyʲ f g
  jgt : g <ʲ f → Bichotomyʲ f g

open Bichotomyʲ

_≟ʲ-suc_ : ∀ {m n} → {b c : Fin (suc n)} → (f g : Inj m n)
          → Trichotomyᶠ b c → Trichotomyʲ f g
          → Trichotomyʲ (inc b f) (inc c g) 
(f ≟ʲ-suc g) _         (jlt f<g) = jlt (<j-suc f<g) 
(f ≟ʲ-suc g) (flt b<c) (jeq f≡g) = jlt (<j-fin f≡g b<c)
(f ≟ʲ-suc g) (feq b≈c) (jeq f≡g) = jeq (cong₂ inc (≈ᶠ→≡ b≈c) f≡g)
(f ≟ʲ-suc g) (fgt c<b) (jeq f≡g) = jgt (<j-fin (sym f≡g) c<b)
(f ≟ʲ-suc g) _         (jgt g<f) = jgt (<j-suc g<f)

_≟ʲ_ : ∀ {m n} → (f g : Inj m n) → Trichotomyʲ f g
nul _ ≟ʲ nul _ = jeq refl
inc b f ≟ʲ inc c g = (f ≟ʲ-suc g) (b ≟ᶠ c) (f ≟ʲ g)

Trichotomy→Bichotomyʲ
  : ∀ {m n} → {f g : Inj m n}
  → Trichotomyʲ f g → Bichotomyʲ f g 
Trichotomy→Bichotomyʲ (jlt f<g) = jle (inl f<g)
Trichotomy→Bichotomyʲ (jeq f≡g) = jle (inr f≡g)
Trichotomy→Bichotomyʲ (jgt g<f) = jgt g<f

_≤?ʲ_ : ∀ {m n} → (f g : Inj m n) → Bichotomyʲ f g 
f ≤?ʲ g = Trichotomy→Bichotomyʲ (f ≟ʲ g)

¬f<f : ∀ {f : Inj m n} → ¬ f <ʲ f
¬f<f {f = inc b g} (<j-suc g<g) = ¬f<f g<g
¬f<f {f = inc b g} (<j-fin _ b<b) = <ᶠ→≢ b<b refl

<ʲ→≢ : ∀ {m n} → {f g : Inj m n}
     → f <ʲ g → f ≢ g
<ʲ→≢ {f = f} f<g f≡g = ¬f<f (subst (f <ʲ_) (sym f≡g) f<g)

≡→≮ʲ : ∀ {m n} → {f g : Inj m n}
     → f ≡ g → ¬ f <ʲ g
≡→≮ʲ f≡g f<g = <ʲ→≢ f<g f≡g

≮ʲ→≡ : ∀ {m n} → {f g : Inj m n}
     → ¬ f <ʲ g → ¬ g <ʲ f → f ≡ g
≮ʲ→≡ {f = nul _} {g = nul _} _ _ = refl
≮ʲ→≡ {f = inc b f} {g = inc c g} f'≮g' g'≮f' with inc b f ≟ʲ inc c g
... | jlt f'<g' = absurd (f'≮g' f'<g')
... | jeq f'≡g' = f'≡g'
... | jgt g'<f' = absurd (g'≮f' g'<f')

discreteInj : Discrete (Inj m n)
discreteInj f g with f ≟ʲ g
... | jlt f<g = no (<ʲ→≢ f<g)
... | jeq f≡g = yes f≡g
... | jgt g<f = no (≢sym (<ʲ→≢ g<f))

isSetInj : isSet (Inj m n)
isSetInj = Discrete→isSet discreteInj
