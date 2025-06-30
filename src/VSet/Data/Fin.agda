module VirtualSet.Fin where

open import 1Lab.Equiv
open import 1Lab.HIT.Truncation using (∃)
open import 1Lab.Path
open import 1Lab.Type
open import 1Lab.Univalence
open import Data.Dec
open import Data.Fin
  renaming (_<_ to _<ꟳ_; _≤_ to _≤ꟳ_; zero to vzero; suc to vsuc)
open import Data.Irr
open import Data.Nat.Base
  renaming (_+_ to _+ℕ_)
open import Data.Nat.Order
open import Data.Nat.Properties
open import Data.Sum
open import Meta.Idiom
open import Prim.Data.Sigma
  using (Σ; Σ-syntax; fst; snd)

open import VirtualSet.Iso

open _≤_

⊎→+ : ∀ {x y : Nat} → (Fin x ⊎ Fin y) → (Fin (x +ℕ y))
⊎→+ {x = zero} (inr i) = i
⊎→+ {x = suc x} {y} (inl i) = inject (+-≤l (suc x) y) i
⊎→+ {x = suc x} (inr i) = fsuc (⊎→+ {x = x} (inr i))

+→⊎ : ∀ {x y : Nat} → (Fin (x +ℕ y)) → (Fin x ⊎ Fin y)
+→⊎ i = split-+ i

decrease-fin : ∀ {y : Nat} (x : Nat) → (a : Fin (x +ℕ y))
             → (a≥x : x ≤ (lower a)) → Fin y
decrease-fin zero a a≥x = a
decrease-fin (suc x) a a≥x with fin-view a
... | vsuc i = decrease-fin x i (≤-peel a≥x)

restrict-fin : ∀ {y : Nat} (x : Nat) → (a : Fin (x +ℕ y))
             → (a<x : lower a < x) → Fin x
restrict-fin x a a<x = fin (lower a) ⦃ forget a<x ⦄

+↔⊎ : ∀ {x y} → Iso (Fin x ⊎ Fin y) (Fin (x +ℕ y))
+↔⊎ = ⊎→+ , 1Lab.Equiv.iso +→⊎ eqr eql
  where
    r⊎→+ : ∀ (x y : Nat) (a : Fin y) → (⊎→+ (inr a)) ≡ fshift x a
    r⊎→+    zero y a = refl 
    r⊎→+ (suc x) y a =
      ⊎→+ (inr a) ≡⟨ refl ⟩
      fsuc (⊎→+ {x} (inr a)) ≡⟨ ap fsuc (r⊎→+ x y a) ⟩
      fsuc (fshift x a) ≡⟨ refl ⟩
      fshift (suc x) a ∎

    l<x : ∀ (x y : Nat) (a : Fin x) → Irr (lower (⊎→+ (inl a)) < x)
    l<x (suc x) y a with fin-view a
    ... | vzero = forget (s≤s 0≤x)
    ... | vsuc (fin a' ⦃ le ⦄) = map (λ a<x → s≤s a<x) le
    
    fshift≡+ : ∀ (x y : Nat) (a : Fin y) → lower (fshift x a) ≡ x +ℕ lower a
    fshift≡+ zero y a = refl
    fshift≡+ (suc x) y a = eq
      where
        eq : lower (fshift (suc x) a) ≡ suc x +ℕ lower a
        eq = lower (fshift (suc x) a) ≡⟨ refl ⟩
             lower (fsuc (fshift x a)) ≡⟨ refl ⟩
             suc (lower (fshift x a)) ≡⟨ ap suc (fshift≡+ x y a) ⟩
             suc x +ℕ lower a ∎

    fshift≡+ᵀ : ∀ (x y : Nat) (a : Fin y)
              → Type
    fshift≡+ᵀ x y a = fshift x a ≡ fin (x +ℕ lower a) ⦃ bounded ⦄ 
      where
        bounded : Irr (x +ℕ lower a < x +ℕ y)
        bounded = +-preserves-<l (lower a) y x <$> Fin.bounded a

    irr-is-prop : (X : Type) → (a b : Irr X) → a ≡ b
    irr-is-prop X a b = refl

    Σ-Fin : (x : Nat) → Type
    Σ-Fin x = Σ[ a ∈ Nat ] Irr (a < x)

    ΣFin≃Fin : ∀ (x : Nat) → Σ-Fin x ≃ Fin x
    ΣFin≃Fin x = {!!}
    
    fshift≡+ꟳ : ∀ (x y : Nat) (a : Fin y) → fshift≡+ᵀ x y a
    fshift≡+ꟳ x y a =
      fshift x a
        ≡⟨ refl ⟩
      fin (lower (fshift x a)) ⦃ Fin.bounded (fshift x a) ⦄
        ≡⟨ ap (λ ○ → fin ○ ⦃ forget {!!} ⦄) eq ⟩
      fin (x +ℕ lower a) ⦃ {!!} ⦄
        ≡⟨ refl ⟩
      fin (x +ℕ lower a) ⦃ bounded ⦄ ∎
      where
        bounded : Irr (x +ℕ lower a < x +ℕ y)
        bounded = +-preserves-<l (lower a) y x <$> Fin.bounded a
        eq : lower (fshift x a) ≡ x +ℕ lower a
        eq = fshift≡+ x y a

    r≥x : ∀ (x y : Nat) (a : Fin x) → Irr (y ≤ lower (⊎→+ (inr a)))
    r≥x x zero a = forget 0≤x
    r≥x x (suc y) a = subst (λ ○ → Irr (suc y ≤ ○)) (sym (fshift≡+ (suc y) x a)) ((le (suc y)))
      where
        le : (y : Nat) → Irr (y ≤ y +ℕ lower a)
        le zero = forget 0≤x
        le (suc y) = s≤s <$> le y

    eql-lemma1 : {x y : Nat} → (a : Fin x) → split-+ (inject (+-≤l x y) a) ≡ inl a
    eql-lemma1 {suc x} {y} a with fin-view a
    ... | vzero = refl
    ... | vsuc a' =
        (split-+ (inject (+-≤l (suc x) y) (fsuc a'))) ≡⟨ refl ⟩
        (split-+ (fsuc (inject (+-≤l x y) a'))) ≡⟨ refl ⟩
        (⊎-map fsuc id (split-+ (inject (+-≤l x y) a')))
          ≡⟨ ap (⊎-map fsuc id) (eql-lemma1 a') ⟩
        (⊎-map fsuc id (inl a'))
          ≡⟨ refl ⟩
        inl (fsuc a') ∎ 

    eql-lemma2 : {x y : Nat} → (a : Fin y) → split-+ (⊎→+ (inr a)) ≡ inr a 
    eql-lemma2 {x = zero} {y} a = refl
    eql-lemma2 {x = suc x} {y} a = refl

    eql : {x y : Nat} → is-left-inverse (+→⊎ {x} {y}) (⊎→+ {x} {y})
    eql {x = zero} {y} (inr a) = refl
    eql {x = suc x} {y} (inl a) = eql-lemma1 a
    eql {x = suc x} {y} (inr a) =
      +→⊎ (fsuc (⊎→+ (inr a)))
        ≡⟨ refl ⟩
      split-+ (fsuc (⊎→+ (inr a)))
        ≡⟨ refl ⟩
      ⊎-map fsuc id (split-+ (⊎→+ (inr a)))
        ≡⟨ ap (⊎-map fsuc id) (eql (inr a)) ⟩
      ⊎-map fsuc id (inr a)
        ≡⟨ refl ⟩
      inr a ∎
    eqr : {x y : Nat} → is-right-inverse +→⊎ ⊎→+
    eqr {x = zero} z = refl
    eqr {x = suc x} z = refl

