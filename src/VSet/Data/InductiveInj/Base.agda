module VSet.Data.InductiveInj.Base where

open import VSet.Prelude
open import Cubical.Data.Prod.Base hiding (map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Properties
open import Cubical.Data.List.Base hiding ([_])

private
  variable
    m n : ℕ

data Inj : ℕ → ℕ → Type where
  nul : ∀ n → Inj 0 n
  inc : ∀ {m n} → (b : Fin (suc n))
      → (inj : Inj m n)
      → Inj (suc m) (suc n)

Injsuc : ℕ → ℕ → Type
Injsuc m n = Inj (suc m) (suc n)

inc-congP : ∀ {m m' n n'}
          → {b : Fin (suc n)} {b' : Fin (suc n')}
          → {f : Inj m n} {f' : Inj m' n'}
          → (meq : m ≡ m') (neq : n ≡ n') (beq : (λ i → Fin (suc (neq i))) [ b ≡ b' ])
          → (feq' : (λ i → Inj (meq i) (neq i)) [ f ≡ f' ])
          → (λ i → cong₂ Injsuc meq neq i) [ (inc {m} {n} b f) ≡ inc {m'} {n'} b' f' ]
inc-congP meq neq beq feq' i =
  inc {meq i} {neq i} (beq i) (feq' i)

inc-cong : ∀ {m n} (b b' : Fin (suc n))
         → (f f' : Inj m n)
         → (beq : b ≡ b') → (feq' : f ≡ f')
         → inc b f ≡ inc b' f'
inc-cong b b' f f' beq feq' = cong₂ inc beq feq'

-- _<ʲ_ : ∀ {m n} (f g : Inj m n) → Type
-- nul _ <ʲ nul _ = ⊥
-- inc b f <ʲ inc c g = {!!}

-- Artificial order for decidability.
-- Lexicographic with first inc inserted taking precidence.
data _<ʲ_ : {m n : ℕ} (f g : Inj m n) → Type where
  <j-suc : {m n : ℕ} → {b c : Fin (suc n)} → {f g : Inj m n}
         → f <ʲ g → inc b f <ʲ inc c g 
  <j-fin : {m n : ℕ} → {b c : Fin (suc n)} → {f g : Inj m n}
         → f ≡ g → b <ᶠ c → inc b f <ʲ inc c g 

open _<ʲ_

data Trichotomyʲ {m n : ℕ} (f g : Inj m n) : Type where
  jlt : f <ʲ g → Trichotomyʲ f g
  jeq : f ≡ g → Trichotomyʲ f g
  jgt : g <ʲ f → Trichotomyʲ f g

open Trichotomyʲ

_≟ʲ-suc_ : ∀ {m n} → {b c : Fin (suc n)} → (f g : Inj m n)
          → Trichotomyᶠ b c → Trichotomyʲ f g
          → Trichotomyʲ (inc b f) (inc c g) 
(f ≟ʲ-suc g) _         (jlt f<g) = jlt (<j-suc f<g) 
(f ≟ʲ-suc g) (flt b<c) (jeq f≡g) = jlt (<j-fin f≡g b<c)
(f ≟ʲ-suc g) (feq b≡c) (jeq f≡g) = jeq (cong₂ inc b≡c f≡g)
(f ≟ʲ-suc g) (fgt c<b) (jeq f≡g) = jgt (<j-fin (sym f≡g) c<b)
(f ≟ʲ-suc g) _         (jgt g<f) = jgt (<j-suc g<f)

_≟ʲ_ : ∀ {m n} → (f g : Inj m n) → Trichotomyʲ f g
nul _ ≟ʲ nul _ = jeq refl
inc b f ≟ʲ inc c g = (f ≟ʲ-suc g) (b ≟ᶠ c) (f ≟ʲ g)

¬f<f : ∀ {f : Inj m n} → ¬ f <ʲ f
¬f<f {f = inc b g} (<j-suc g<g) = ¬f<f g<g
¬f<f {f = inc b g} (<j-fin _ b<b) = <ᶠ→≢ b<b refl

<ʲ→≢ : ∀ {m n} → (f g : Inj m n)
     → f <ʲ g → f ≢ g
<ʲ→≢ f g f<g f≡g = ¬f<f (subst (f <ʲ_) (sym f≡g) f<g)

inc-inj : ∀ {m n} (b b' : Fin (suc n))
        → (f f' : Inj m n)
        → inc b f ≡ inc b' f'
        → (b ≡ b') × (f ≡ f')
inc-inj b b' f f' bf≡b'f' with b ≟ᶠ b'
... | flt b<b' = {!!} , {!!}
... | fgt b'<b = {!!} , {!!}
... | feq b≡b' = {!!} , {!!}

-- inc-inj fzero fzero f f' bf≡b'f' = refl , {!!}
-- inc-inj fzero (fsuc b') f f' bf≡b'f' =
--   absurd {A = λ _ → (fzero ≡ fsuc b') × (f ≡ f')} (subst P bf≡b'f' tt)
--   where
--     P : Inj m n → Type
--     P (nul _) = ⊥
--     P (inc fzero h) = ⊤
--     P (inc (fsuc b) h) = ⊥
-- inc-inj (fsuc b) fzero f f' bf≡b'f' =
--   absurd {A = λ _ → (fsuc b ≡ fzero) × (f ≡ f')} (subst P bf≡b'f' tt)
--   where
--     P : Inj m n → Type
--     P (nul _) = ⊥
--     P (inc fzero h) = ⊥
--     P (inc (fsuc b) h) = ⊤ 
-- inc-inj (fsuc b) (fsuc b') f f' bf≡b'f' =
--   let 
--     c = (cong
--     b≡b'xf≡f' = inc-inj (finject 1 b) (finject 1 b') f f' ?
--   in {! ?!}


-- _≟ʲ_ : ∀ {m n} 
--         → (f f' : Inj m n)
--         → Dec (f ≡ f')
-- nul _ ≟ʲ nul _ = yes refl
-- inc b f ≟ʲ inc b' f' with b ≟ᶠ b' | f ≟ʲ f'
-- ... | flt b<b' | _ = no λ bf≡b'f' → {!!}
-- ... | fgt b'<b | _ = no λ bf≡b'f' → {!!}
-- ... | feq b≡b' | v = {!!}


discreteInj : Discrete (Inj m n)
discreteInj (nul n) (nul n) = yes refl
discreteInj (inc b f) (inc c g) with b ≟ᶠ c | discreteInj f g
... | b=c? | yes p = {!!}
... | b=c? | no f≢g = no λ b-f≡c-g → f≢g {!!}

-- with ? f g
-- ... | yes p = yes ? 
-- ... | no ¬p = no ?

isSetInj : isSet (Inj m n)
isSetInj = Discrete→isSet discreteInj

Inj-isSet : isSet (Inj m n)
Inj-isSet (nul n) (nul n) p q = {!!}
Inj-isSet (inc b f) g p q = {!!}

inc-bigger : ∀ {n} → (b : Fin (suc n)) → (a : Fin n) → Fin (suc n)
inc-bigger fzero a = fsuc a
inc-bigger (fsuc b) fzero = fzero
inc-bigger (fsuc b) (fsuc a) = fsuc (inc-bigger b a)

apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc b inj) fzero = b
apply (inc b inj) (fsuc a) =
  inc-bigger b (apply inj a)

to-list : Inj m n → List (Fin n)
to-list (nul _) = []
to-list (inc b f) =
  b ∷ map (inc-bigger b) (to-list f)

idInj : ∀ m → Inj m m
idInj zero = nul zero
idInj (suc m) = inc fzero (idInj m)

cross : Inj 2 2
cross = inc (fsuc fzero) $ inc fzero $ nul 0

-- eg. cycle-l 5 = (5 0 1 2 3 4)
cycle-l : ∀ m → Inj (suc m) (suc m)
cycle-l m = inc fmax (idInj m)

-- eg. cycle-r 5 = (1 2 3 4 5 0)
cycle-r : ∀ m → Inj (suc m) (suc m)
cycle-r zero = idInj 1
cycle-r (suc m) = inc (fsuc fzero) (cycle-r m)

c1 = to-list (cycle-r 3)
c2 = to-list (cycle-l 3)
