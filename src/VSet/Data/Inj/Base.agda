module VSet.Data.Inj.Base where

open import VSet.Prelude
open import Cubical.Data.Prod.Base hiding (map)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
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

jcast : ∀ {m m' n n' : ℕ} → m ≡ m' → n ≡ n' → Inj m n → Inj m' n'
jcast {zero} {zero} {n} {n'} p q (nul _) = nul _
jcast {zero} {suc m'} {n} {n'} p q (nul _) = absurd (znots p)
jcast {suc m} {zero} {suc n} {n'} p q (inc b f) = absurd (snotz p)
jcast {suc m} {suc m'} {suc n} {zero} p q (inc b f) = absurd (snotz q)
jcast {suc m} {suc m'} {suc n} {suc n'} p q (inc b f) =
  inc (fcast q b) (jcast (injSuc p) (injSuc q) f)

jcast-loop : ∀ {m n : ℕ} (p : m ≡ m) (q : n ≡ n)
           → (f : Inj m n) → jcast p q f ≡ f
jcast-loop p q (nul _) = refl
jcast-loop p q (inc b f) =
  cong₂ inc (fcast-loop q b)
        (jcast-loop (injSuc p) (injSuc q) f)

apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc b inj) fzero = b
apply (inc b inj) (fsuc a) =
  fsplice b (apply inj a)

to-list : Inj m n → List (Fin n)
to-list (nul _) = []
to-list (inc b f) =
  b ∷ map (fsplice b) (to-list f)

_∈ʲ_ : ∀ {n m : ℕ} → (b : Fin n) → (Inj m n) → Type
b ∈ʲ f = Σ[ a ∈ Fin _ ] apply f a ≡ b

_∉ʲ_ : ∀ {n m : ℕ} → (b : Fin n) → (Inj m n) → Type
b ∉ʲ f = ¬ b ∈ʲ f

idInj : ∀ m → Inj m m
idInj zero = nul zero
idInj (suc m) = inc fzero (idInj m)

𝟙 : ∀ {m} → Inj m m
𝟙 {m} = idInj m

cross : Inj 2 2
cross = inc (fsuc fzero) $ inc fzero $ nul 0

-- eg. cycle-l 5 = (5 0 1 2 3 4)
cycle-l : ∀ m → Inj (suc m) (suc m)
cycle-l m = inc fmax (idInj m)

-- eg. cycle-r 5 = (1 2 3 4 5 0)
cycle-r : ∀ m → Inj (suc m) (suc m)
cycle-r zero = idInj 1
cycle-r (suc m) = inc (fsuc fzero) (cycle-r m)

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
