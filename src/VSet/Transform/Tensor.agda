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
tensor {W} {X} {Y} {Z} f g = ↔to↣ (⊎↔+ X Z) ↣∘↣ ↣-map-⊎ f g ↣∘↣ ↔to↣ (flip-↔ (⊎↔+ W Y))

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
      → ⊎→+ X Z (⊎-map (subst Fin p) (subst Fin q) (+→⊎ W Y u))
      ≡ subst Fin (cong₂ _+_ p q) u
    ⊎-map-respects-transport {zero} {zero} {suc Y} {suc Z} p q fzero =
      ⊎→+ zero (suc Z) (⊎-map (subst Fin p) (subst Fin q) (+→⊎ zero (suc Y) fzero))
        ≡⟨ refl ⟩
      ⊎→+ zero (suc Z) (⊎-map (subst Fin p) (subst Fin q) (inr fzero))
        ≡⟨ refl ⟩
      ⊎→+ zero (suc Z) (inr (subst Fin q (fzero {Y})))
        ≡⟨ cong (⊎→+ zero (suc Z) ∘ inr)
                (sym {!fzero≡subst-fzero ?!}) ⟩
      ⊎→+ zero (suc Z) (inr (fzero {Z}))
        ≡⟨ refl ⟩
      fshift zero {suc Z} (fzero {Z})
        ≡⟨ refl ⟩
      fzero {0 + Z}
        ≡⟨ fzero≡subst-fzero (injSuc q) ⟩
      subst (Fin ∘ suc) (injSuc q) fzero
        ≡⟨ refl ⟩
      subst Fin (cong suc (injSuc q)) fzero
        ≡⟨ cong (λ ○ → subst Fin (cong suc ○) fzero) {!pred∘suc≡id!} ⟩
      subst Fin (cong suc (injSuc q)) fzero
        ≡⟨ {!fzero≡subst-fzero ?!} ⟩
      subst Fin (cong₂ _+_ p q) fzero ▯
    ⊎-map-respects-transport {zero} {zero} {Y} {Z} p q (fsuc u) = {!!}
    ⊎-map-respects-transport {suc W} {suc X} {Y} {Z} p q u = {!!}
    ⊎-map-respects-transport {zero} {suc X} {Y} {Z} p q u = absurd (znots p)
    ⊎-map-respects-transport {suc W} {zero} {Y} {Z} p q u = absurd (snotz p)
    ⊎-map-respects-transport {zero} {zero} {Y} {Z} p q fzero = {!!}
    
    --   with +→⊎ W Y u | inspect (+→⊎ W Y) u 
    -- ... | inl x | [ path ]ᵢ = {!!}


      -- ⊎→+ (⊎-map (subst Fin p) (subst Fin q) (inl x))
      --   ≡⟨ refl ⟩
      -- ⊎→+ (inl (subst Fin p x))
      --   ≡⟨ refl ⟩
      -- finject Z (subst Fin p x)
      --   ≡⟨ sym (subst-finject-reorder Z p x) ⟩
      -- transport (λ i → ⟦ p i + Z ⟧) (finject Z x)
      --   ≡⟨ (let A' = A in {!!}) ⟩
      -- subst Fin (cong₂ _+_ p q) u ▯
      --   where u≡x : u ≡ finject Y x
      --         u≡x =
    -- ... | inr x | [ A ]ᵢ = {!!}

    f⊕g≡transport : fst (f ⊕ g) ≡ subst Fin W+Y≡X+Z
    f⊕g≡transport =
      fst (f ⊕ g)
        ≡⟨ refl ⟩
      fst (↔to↣ (⊎↔+ X Z) ↣∘↣ ↣-map-⊎ f g ↣∘↣ ↔to↣ (flip-↔ (⊎↔+ W Y)))
        ≡⟨ refl ⟩
      ⊎→+ X Z ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ W Y
        ≡⟨ cong₂ (λ ○ □ → ⊎→+ X Z ∘ ⊎-map ○ □ ∘ +→⊎ W Y) f≡transport g≡transport ⟩
      ⊎→+ X Z ∘ ⊎-map (subst Fin p) (subst Fin q) ∘ +→⊎ W Y
        ≡⟨ {!!} ⟩
      subst Fin W+Y≡X+Z ▯

