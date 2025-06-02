module FinSetoid.Properties where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.List
  using (List; []; _∷_; _++_; filter; map)
import Data.List.Membership.Setoid
open import Data.List.NonEmpty
  using (List⁺) renaming (_∷_ to _∷⁺_)
open import Data.List.Relation.Unary.All as All
  using (All; all?)
open import Data.List.Relation.Unary.Any as Any
  using (Any; map; here; there)
open import Data.Product
  using (Σ-syntax; _×_; proj₁; proj₂)
open import Data.Product.Base as Product
  using (∃; _×_; _,_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Level
  using (_⊔_; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.Bundles
  using (DecSetoid; Setoid)
open import Function.Bundles
  using (_⇔_; Equivalence)
open import Relation.Binary.Definitions
  using (Decidable; _Respects_)
open import Relation.Binary.Morphism.Bundles 
  using (SetoidHomomorphism)
open import Relation.Nullary.Decidable.Core
  using (yes; no; _×-dec_ )
open import Relation.Nullary.Negation
  using (¬_)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Antisymmetric;
         _Respectsˡ_; _Respectsʳ_; _Respects_;
         Decidable)
open import Relation.Binary.Structures
  using (IsEquivalence)
import Relation.Binary.PropositionalEquality.Core as ≡
  using (refl; sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_)


open import FinSetoid.Base

private
  variable
    c ℓ : Level.Level

module _ {Dom : DecSetoid c ℓ} where
  open DecSetoid Dom renaming (Carrier to D) 
  open import Data.List.Membership.DecSetoid Dom

  open import Data.List.Properties using (++-assoc)

  ∈-resp-≈ : {P : FiniteSet} → {x y : D} → x ≈ y → x ∈ P → y ∈ P
  ∈-resp-≈ {p ∷ ps} x≈y (here x≈p) = here (trans (sym x≈y) x≈p)
  ∈-resp-≈ {p ∷ ps} x≈y (there x∈P) = there (∈-resp-≈ x≈y x∈P)

  x∈P++x++Q : (ps qs : List D) → (x : D) → x ∈ ps ++ (x ∷ qs)
  x∈P++x++Q [] qs x = here refl
  x∈P++x++Q (p ∷ ps) qs x = there (x∈P++x++Q ps qs x)
  

  Q⊆P++Q : (ps qs : List D) → qs ⊆ (ps ++ qs)
  Q⊆P++Q [] [] = All.[]
  Q⊆P++Q [] (q ∷ qs) = here refl All.∷ Q⊆P++Q (q ∷ []) qs
  Q⊆P++Q (p ∷ ps) [] = All.[]
  Q⊆P++Q (p ∷ ps) (q ∷ qs)  =
    there (x∈P++x++Q ps qs q) All.∷ ≡.subst (λ xs → qs ⊆ (p ∷ xs)) (++-assoc ps (q ∷ []) qs) recurse
      where recurse : qs ⊆ (p ∷ ps ++ (q ∷ [])) ++ qs
            recurse = (Q⊆P++Q (p ∷ ps ++ (q ∷ [])) qs)

  ⊆-refl : {P : FiniteSet} → P ⊆ P
  ⊆-refl {P} = Q⊆P++Q [] P

  ⊆-resp-∈ : {P Q : List D} → P ⊆ Q → (x : D) → x ∈ P → x ∈ Q
  ⊆-resp-∈ {p ∷ ps} {qs} (p∈qs All.∷ _) x (here x≈p) =
    ∈-resp-≈ (sym x≈p) p∈qs 
  ⊆-resp-∈ {p ∷ ps} {qs} (_ All.∷ ps⊆qs) x (there p∈qs) =
    ⊆-resp-∈ {ps} {qs} ps⊆qs x p∈qs

  -- Probably could tidy this up a bit.
  ⊆-trans : {P Q R : List D} → P ⊆ Q → Q ⊆ R → P ⊆ R
  ⊆-trans All.[] qs⊆rs = All.[]
  ⊆-trans {p ∷ ps} {q ∷ qs} {rs} (here p≈q All.∷ ps⊆qqs) (q∈rs All.∷ qs⊆rs)
    = ∈-resp-≈ p≈q q∈rs All.∷ ⊆-trans ps⊆qqs (q∈rs All.∷ qs⊆rs)
  ⊆-trans {p ∷ ps} {q ∷ qs} {rs} (there p∈qs All.∷ ps⊆qs) (q∈rs All.∷ qs⊆rs) =
          ⊆-resp-∈ (q∈rs All.∷ qs⊆rs) p (there p∈qs)
    All.∷ ⊆-trans {ps} {q ∷ qs} {rs} ps⊆qs (q∈rs All.∷ qs⊆rs)

  ++≐∪ : (P Q : FiniteSet) → Q ++ P ≐ P ∪ Q
  ++≐∪ ps [] = Q⊆P++Q [] ps , Q⊆P++Q [] ps
  ++≐∪ ps (q ∷ qs) with q ∈? ps
  ... | yes q∈ps = {!!} , {!!}
        where Q⊆Q++ps : ps ⊆ (q ∷ qs) ++ ps
              Q⊆Q++ps = Q⊆P++Q (q ∷ qs) ps
              qs⊆qs∪ps : qs ++ ps ⊆ ps ∪ qs 
              qs⊆qs∪ps = proj₁ (++≐∪ ps {!qs!})
  ... | no _ = {!!}

  result2 : (P Q : FiniteSet) → (x : D) → x ∈ P → x ∈ P ∪ Q
  result2 P [] x x∈P = x∈P
  result2 (p ∷ ps) (q ∷ Q) x x∈P with x ≟ q | result2 (p ∷ ps) Q
  result2 (p ∷ ps) (q ∷ Q) x (here x≈p) | yes x≈q | A = {!!}
  result2 (p ∷ ps) (q ∷ Q) x (there x∈P) | yes x≈q | A = {!!}
  ... | no x≈q | A = {!there ?!}

  result1 : {P Q : FiniteSet} → {x q : D} → q ∈ P → x ∈ P ∪ (q ∷ Q) → x ∈ P ∪ Q
  result1 {P} {Q} {x} {q} q∈P x∈P∪qQ with (x ∈? P)
  result1 {p ∷ ps} {_} {_} {_} q∈P x∈P∪qQ | yes (here x≈p) = {!!}
  result1 {P} {_} {_} {_} q∈P x∈P∪qQ | yes (there x∈P) = {!!}
  result1 {P} {Q} {x} {q} q∈P x∈P∪qQ | no _ = {!!}

  ∪-transports-∈ˡ : {P Q : FiniteSet} → {x : D} → x ∈ P → x ∈ P ∪ Q
  ∪-transports-∈ˡ {ps} {[]} {x} x∈P = x∈P
  ∪-transports-∈ˡ {ps} {q ∷ qs} {x} x∈P with q ∈? ps
  ∪-transports-∈ˡ {ps} {q ∷ qs} {x} x∈P  | yes q∈ps
                 with ∪-transports-∈ˡ {P = ps} {Q = qs} x∈P | x ≟ q
  ∪-transports-∈ˡ {ps} {q ∷ qs} {x} x∈P  | yes q∈ps | A | yes x≈q =
    let x∈ps = ∈-resp-≈ (sym x≈q) q∈ps in {!A!}
  ∪-transports-∈ˡ {ps} {q ∷ qs} {x} x∈P  | yes q∈ps | A | no _ = {!!}
  ∪-transports-∈ˡ {ps} {q ∷ qs} {x} x∈P  | no _  = ∪-transports-∈ˡ {!!} -- {P = q ∷ ps} {Q = qs} (there x∈P)

  ∪-transports-∈ʳ : {P Q : FiniteSet} → {x : D} → x ∈ Q → x ∈ P ∪ Q
  ∪-transports-∈ʳ {ps} {q ∷ qs} {x} x∈Q with (q ∈? ps)
  ∪-transports-∈ʳ {ps} {q ∷ qs} {x} (here x≈q) | yes q∈ps = 
    let
      x∈ps : x ∈ ps
      x∈ps = ∈-resp-≈ (sym x≈q) q∈ps
    in {!!} -- ∪-transports-∈ˡ {Q = qs} x∈ps
  ∪-transports-∈ʳ {ps} {q ∷ qs} {x} (there x∈qs) | yes _ =
    {!!} -- ∪-transports-∈ʳ {Q = qs} x∈qs
  ∪-transports-∈ʳ {ps} {q ∷ qs} {x} (here x≈q) | no _ =
    {!!} -- ∪-transports-∈ˡ{P = q ∷ ps} {Q = qs} (here x≈q)
  ∪-transports-∈ʳ {ps} {q ∷ qs} {x} (there x∈qs) | no _ =
    {!!} -- ∪-transports-∈ʳ {P = q ∷ ps} {Q = qs} x∈qs

--   ⊎→∪ : {P Q : FiniteSet} → {x : D} → x ∈ P ⊎ x ∈ Q → x ∈ P ∪ Q
--   ⊎→∪ (inj₁ x∈P) = ∪-transports-∈ˡ x∈P
--   ⊎→∪ (inj₂ x∈Q) = ∪-transports-∈ʳ x∈Q
-- 
--   ∪→⊎ : {P Q : FiniteSet} → {x : D} → x ∈ P ∪ Q → x ∈ P ⊎ x ∈ Q
--   ∪→⊎ {P = ps} {Q = []} x∈P∪Q = inj₁ x∈P∪Q
--   ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q with q ∈? ps | x ≟ q 
--   ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | yes x≈q = inj₂ (here x≈q)
--   ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | no _ with (∪→⊎ {P = ps} {Q = qs} x∈P∪Q)
--   ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | no _ | inj₁ x∈ps =
--     inj₁ x∈ps
--   ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | no _ | inj₂ x∈qs =
--     inj₂ (there x∈qs)
--   ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | no _ | yes x≈q = inj₂ (here x≈q)
--   ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | no _ | no _ with (∪→⊎ {P = q ∷ ps} {Q = qs} x∈P∪Q)
--   ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | no _ | no ¬x≈q | inj₁ (here x≈q) =
--     ⊥-elim (¬x≈q x≈q)
--   ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | no _ | no ¬x≈q | inj₁ (there x∈ps) =
--     inj₁ x∈ps
--   ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | no _ | no _ | inj₂ x∈qs = inj₂ (there x∈qs)
-- 
--   ∅⊆P : (P : FiniteSet) → ∅ ⊆ P
--   ∅⊆P P = All.[]
-- 
--   ∈→⊆ : (P : FiniteSet) → (x : D) → x ∈ P → ｛ x ｝ ⊆ P
--   ∈→⊆ ps x x∈ps = x∈ps All.∷ All.[]
-- 
--   ⊆→∈ : (P : FiniteSet) → (x : D) → ｛ x ｝ ⊆ P → x ∈ P
--   ⊆→∈ P x (x∈P All.∷ _) = x∈P
-- 
--   ∈→∈→⊆ : (P Q : FiniteSet) → (∀ (x : D) → x ∈ P → x ∈ Q) → P ⊆ Q
--   ∈→∈→⊆ [] qs f = All.[]
--   ∈→∈→⊆ (p ∷ ps) qs f = f p (here refl) All.∷ ∈→∈→⊆ ps qs f′
--     where f′ : ∀ (x : D) → x ∈ ps → x ∈ qs
--           f′ x x∈ps = f x (there x∈ps)
-- 
--   ⊆→∈→∈ : (P Q : FiniteSet) → P ⊆ Q → (∀ (x : D) → x ∈ P → x ∈ Q)
-- 
--   ⊆→∈→∈ (p ∷ ps) qs (p∈qs All.∷ ps⊆qs) x (here x≈p) =
--     ∈-resp-≈ (sym x≈p) p∈qs
--   ⊆→∈→∈ (p ∷ ps) qs (p∈qs All.∷ ps⊆qs) x (there x∈ps) =
--     ⊆→∈→∈ ps qs ps⊆qs x x∈ps
-- 
--   ∪-commutes′ : (P Q : FiniteSet) → P ∪ Q ⊆ Q ∪ P
--   ∪-commutes′ P Q = ∈→∈→⊆ (P ∪ Q) (Q ∪ P) f
--     where f : ∀ (x : D) → x ∈ P ∪ Q → x ∈ Q ∪ P
--           f x x∈P∪Q with ∪→⊎ x∈P∪Q
--           ... | inj₁ x∈P = ∪-transports-∈ʳ x∈P
--           ... | inj₂ x∈Q = ∪-transports-∈ˡ x∈Q
--   ∪-commutes : (P Q : FiniteSet) → P ∪ Q ≐ Q ∪ P
--   ∪-commutes P Q = ∪-commutes′ P Q , ∪-commutes′ Q P
  
