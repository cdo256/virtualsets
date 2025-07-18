module VSet.Transform.Tensor where

open import VSet.Prelude
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import Cubical.Data.Nat.Properties

open import VSet.Data.Nat using (ℕ; zero; suc)
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Injection
open import VSet.Data.SomeFin.Equality
open import VSet.Data.SomeFin.Properties
open import VSet.Transform.Split
open import VSet.Transform.Pred

tensor : ∀ {W X Y Z : SomeFin} → [ W ↣ X ] → [ Y ↣ Z ] → [ W + Y ↣ X + Z ]
tensor {W} {X} {Y} {Z} f g = ↔to↣ ⊎↔+ ↣∘↣ ↣-map-⊎ f g ↣∘↣ ↔to↣ (flip-↔ ⊎↔+)

[id] : {X : SomeFin} → [ X ↣ X ]
[id] {X} = ↣-id ⟦ X ⟧

𝟘 : [ 0 ↣ 0 ]
𝟘 = ↣-id ⟦ 0 ⟧


infixl 30 _⊕_

_⊕_ : ∀ {W X Y Z : SomeFin} → [ W ↣ X ] → [ Y ↣ Z ] → [ W + Y ↣ X + Z ]
f ⊕ g = tensor f g

ladd : ∀ {X Y : SomeFin} → (A : SomeFin) → [ X ↣ Y ] → [ A + X ↣ A + Y ]
ladd {X} {Y} A f = (↣-id ⟦ A ⟧) ⊕ f

radd : ∀ {X Y : SomeFin} → (A : SomeFin) → [ X ↣ Y ] → [ X + A ↣ Y + A ]
radd {X} {Y} A f = f ⊕ (↣-id ⟦ A ⟧)

is-transport : ∀ {X Y : SomeFin} → (f : [ X ↣ Y ]) → Type
is-transport {X} {Y} f = Σ[ p ∈ X ≡ Y ] fst f ≡ fst (≈transport refl p (↣-id ⟦ X ⟧))

transport-tensor : ∀ {W X Y Z : SomeFin}
                   → (f : [ W ↣ X ]) → (g : [ Y ↣ Z ])
                   → is-transport f → is-transport g
                   → is-transport (f ⊕ g)
transport-tensor {W} {X} {Y} {Z} f g (p , f≡transport) (q , g≡transport) =
  W+Y≡X+Z , f⊕g≡transport
  where
    W+Y≡X+Z : W + Y ≡ X + Z
    W+Y≡X+Z = cong₂ _+_ p q

    shrink-subst : ∀ {U V : SomeFin} (p : U ≡ V)
                 → subst Fin p ∘ id ∘ subst Fin refl ≡ subst Fin p
    shrink-subst {U} {V} p =
      subst Fin p ∘ id ∘ subst Fin refl ≡⟨ (cong (λ ○ → subst Fin p ∘ id ∘ ○)) (funExt transportRefl) ⟩
      subst Fin p ∘ id ∘ id ≡⟨ refl ⟩
      subst Fin p ▯

    ⊎-map-respects-transport
      : ∀ {W X Y Z : SomeFin} (p : W ≡ X) (q : Y ≡ Z) (u : ⟦ W + Y ⟧)
      → ⊎→+ (⊎-map (subst Fin p) (subst Fin q) (+→⊎ {X = W} {Y = Y} u))
      ≡ subst Fin (cong₂ _+_ p q) u
    ⊎-map-respects-transport {W} {X} {Y} {Z} p q u with +→⊎ {X = W} u
    ... | inl x =
      ⊎→+ (⊎-map (subst Fin p) (subst Fin q) (inl x))
        ≡⟨ refl ⟩
      ⊎→+ (inl (subst Fin p x))
        ≡⟨ refl ⟩
      finject Z (subst Fin p x)
        ≡⟨ {!!} ⟩
      finject Z (subst Fin p x)
        ≡⟨ {!!} ⟩
      subst (λ ○ → ⟦ ○ + Z ⟧) p (finject Z x)
        ≡⟨ {!refl!} ⟩
      subst (λ ○ → ⟦ ○ + Z ⟧) p (⊎→+ (inl x))
        ≡⟨ {!!} ⟩
      {!!} ▯
    ... | inr x = {!!}

    f⊕g≡transport : fst (f ⊕ g) ≡
                    fst (≈transport refl W+Y≡X+Z (↣-id ⟦ W + Y ⟧))
    f⊕g≡transport =
      fst (f ⊕ g) ≡⟨ refl ⟩
      fst (↔to↣ ⊎↔+ ↣∘↣ ↣-map-⊎ f g ↣∘↣ ↔to↣ (flip-↔ ⊎↔+)) ≡⟨ refl ⟩
      ⊎→+ ∘ ⊎-map (fst f) (fst g) ∘ +→⊎
        ≡⟨ (cong (λ ○ → ⊎→+ ∘ ⊎-map ○ (fst g) ∘ +→⊎)) f≡transport ⟩
      ⊎→+ ∘ ⊎-map (fst (≈transport refl p (↣-id ⟦ W ⟧))) (fst g) ∘ +→⊎
        ≡⟨ (cong (λ ○ → ⊎→+ ∘ ⊎-map (fst (≈transport refl p (↣-id ⟦ W ⟧))) ○ ∘ +→⊎)) g≡transport ⟩
      ⊎→+ ∘ ⊎-map (fst (≈transport refl p (↣-id ⟦ W ⟧)))
                  (fst (≈transport refl q (↣-id ⟦ Y ⟧))) ∘ +→⊎
        ≡⟨ refl ⟩
      ⊎→+ ∘ ⊎-map (≈transport-fun refl p id)
                  (≈transport-fun refl q id) ∘ +→⊎
        ≡⟨ refl ⟩
      ⊎→+ ∘ ⊎-map (subst Fin p ∘ id ∘ subst Fin refl)
                  (subst Fin q ∘ id ∘ subst Fin refl) ∘ +→⊎
        ≡⟨ (cong₂ (λ ○ □ → ⊎→+ {X = X} {Y = Z}
                         ∘ ⊎-map ○ □
                         ∘ +→⊎ {X = W} {Y = Y}))
                  (shrink-subst p) (shrink-subst q) ⟩
      ⊎→+ ∘ ⊎-map (subst Fin p) (subst Fin q) ∘ +→⊎
        ≡⟨ {!!} ⟩
      subst Fin W+Y≡X+Z
        ≡⟨ sym (shrink-subst W+Y≡X+Z) ⟩
      subst Fin W+Y≡X+Z ∘ id ∘ subst Fin refl
        ≡⟨ refl ⟩
      fst (≈transport refl W+Y≡X+Z (↣-id ⟦ W + Y ⟧)) ▯

