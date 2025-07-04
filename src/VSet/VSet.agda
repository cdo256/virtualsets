module VSet.VSet where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties

open import VSet.Path
open import VSet.Data.Fin.Default
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties
open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Properties
open import VSet.Data.SomeFin.Injection
open import VSet.Transform.Pred
open import VSet.Transform.Sub
open import VSet.Transform.Split

{-

module _ where
  open Injection 


_+ᶠ_ : ∀ {X Y : SomeFin} (g : Fin X ↣ Fin Y) → (A : SomeFin) → Fin (X + A) ↣ Fin (Y + A)
_+ᶠ_ {X} {Y} g A =
  subst (λ h → Fin (X + A) ↣ Fin h)
          (sym (+-comm Y A))
    (subst (λ h → Fin h ↣ Fin (A + Y))
             (sym (+-comm X A))
       (g +ᶠ-sym A))

_⊙_ : ∀ {X Y fzero} → (Fin Y ↣ Fin fzero) → (Fin X ↣ Fin Y) → (Fin X ↣ Fin fzero)
_⊙_ g f = record
  { fst = fst g ∘ fst f 
  ; cong = cong g ∘ cong f
  ; injective = injective f ∘ injective g
  }

module theorem1-2 where
  private
    variable A B X Y fzero : SomeFin

  lemma1-3 : ∀ (f : Fin X ↣ Fin Y) → (f +ᶠ A) -ᶠ A ≡ f
  lemma1-3 {A = zero} f = 
    begin
        f +ᶠ zero -ᶠ zero
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ {!!} ⟩
        f ∎

  lemma1-3 {A = suc A} f = {!!}

  --lemma1-3 : ∀ {X Y : SomeFin} → (f : Fin (X + 0) ↣ Fin (Y + 0)) → (f -ᶠ 0) ≡ f

  --lemma1 : ∀ {A X Y fzero} → (f : Fin (Y + A) ↣ Fin (fzero + A)) → (g : Fin X ↣ Fin Y) → (f ⊙ (g +ᶠ A)) -ᶠ A ≡ (f -ᶠ A) ⊙ g 
  --lemma1 {zero} {X} {Y} {fzero} f g = 
  --  begin
  --      ((f ⊙ (g +ᶠ 0)) -ᶠ 0)
  --    ≡⟨ {!!} ⟩
  --      {!!}
  --    ≡⟨ {!!} ⟩
  --      ((f -ᶠ 0) ⊙ g ) ∎

  --lemma1 {suc A} {X} {Y} {fzero} f g = {!!}
  --  -- begin
  --  --     ((f ⊙ (g +ᶠ A)) -ᶠ A)
  --  --   ≡⟨ {!!} ⟩
  --  --     ((f -ᶠ A) ⊙ g ) ∎
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
