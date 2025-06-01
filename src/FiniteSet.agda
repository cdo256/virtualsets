module FiniteSet where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.List
  using (List; []; _∷_; filter; map)
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
open import Relation.Binary.Structures
  using (IsEquivalence)

private
  variable
    c ℓ : Level.Level

module _ {Dom : DecSetoid c ℓ} where
  open DecSetoid Dom renaming (Carrier to D) 
  open import Data.List.Membership.DecSetoid Dom
  
  FiniteSet : Set c
  FiniteSet = List D

  ∅ : FiniteSet
  ∅ = []
  
  ｛_｝ : D → FiniteSet
  ｛ x ｝ = x ∷ []

  infix 4 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_ _≐_ _≐?_
  
  _⊆_ : FiniteSet → FiniteSet → Set _
  P ⊆ Q = All (_∈ Q) P

  _⊆?_ : Decidable _⊆_
  P ⊆? Q = all? (_∈? Q) P

  _⊇_ : FiniteSet → FiniteSet → Set _
  P ⊇ Q = Q ⊆ P
  
  _⊈_ : FiniteSet → FiniteSet → Set _
  P ⊈ Q = ¬ (P ⊆ Q)
  
  _⊉_ : FiniteSet → FiniteSet → Set _
  P ⊉ Q = ¬ (P ⊇ Q)
  
  _⊂_ : FiniteSet → FiniteSet → Set _
  P ⊂ Q = P ⊆ Q × Q ⊈ P
  
  _⊃_ : FiniteSet → FiniteSet → Set _
  P ⊃ Q = Q ⊂ P
  
  _⊄_ : FiniteSet → FiniteSet → Set _
  P ⊄ Q = ¬ (P ⊂ Q)
  
  _⊅_ : FiniteSet → FiniteSet → Set _
  P ⊅ Q = ¬ (P ⊃ Q)
  
  _≐_ : FiniteSet → FiniteSet → Set _
  P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

  _≐?_ : Decidable (_≐_)
  P ≐? Q = (P ⊆? Q) ×-dec (Q ⊆? P)


  infix 10 ⋃ ⋂
  infixr 7 _∩_
  infixr 6 _∪_
  infixr 6 _∖_

  -- \un
  _∪_ : FiniteSet → FiniteSet → FiniteSet
  P ∪ [] = P
  P ∪ (x ∷ Q) with (x ∈? P)
  ... | yes z = P ∪ Q
  ... | no z = (x ∷ P) ∪ Q
  
  -- \cap
  _∩_ : FiniteSet → FiniteSet → FiniteSet
  P ∩ Q = filter (_∈? Q) P

  -- \setminus
  _∖_ : FiniteSet → FiniteSet → FiniteSet
  P ∖ Q = filter (_∉? Q) P
  
  -- \bigcup
  ⋃ : List FiniteSet → FiniteSet
  ⋃ [] = []
  ⋃ (P ∷ I) = P ∪ ⋃ I

  -- \bigcap
  ⋂ : List⁺ FiniteSet → FiniteSet
  ⋂ (P ∷⁺ I) = intersect P I
    where 
      intersect : FiniteSet → List FiniteSet → FiniteSet
      intersect P [] = P
      intersect P (Q ∷ I) = intersect (P ∩ Q) I
  
  disjoint : FiniteSet → FiniteSet → Set _
  disjoint P Q = P ∩ Q ≐ ∅
  
  _+_ : ∀ (P Q : FiniteSet) → {_ : disjoint P Q} → FiniteSet
  P + Q = P ∪ Q

  _-_ : ∀ (P Q : FiniteSet) → {_ : Q ⊆ P} → FiniteSet
  P - Q = P ∖ Q 

  toSet : (P : FiniteSet) → Set _
  toSet P = Σ[ x ∈ D ] (x ∈ P)

  module _ where
    open import Relation.Binary.Structures
    -- open IsEquivalence isEquivalence
    toSetoid : (P : FiniteSet) → Setoid _ _
    toSetoid P = record
      { Carrier = Σ[ x ∈ D ] (x ∈ P)
      ; _≈_ = λ (x , _) (y , _) → x ≈ y
      ; isEquivalence = record
        { refl = refl
        ; sym = sym 
        ; trans = trans 
        }
      }

    infixr 0 _→′_ 
  
    _→′_ : (P Q : FiniteSet) → Set _
    P →′ Q = SetoidHomomorphism (toSetoid P) (toSetoid Q)
    
    open SetoidHomomorphism using (⟦_⟧) public

  ≈-preserves-∈ : {P : FiniteSet} → {x y : D} → x ≈ y → x ∈ P → y ∈ P
  ≈-preserves-∈ {p ∷ ps} x≈y (here x≈p) = here (trans (sym x≈y) x≈p)
  ≈-preserves-∈ {p ∷ ps} x≈y (there x∈P) = there (≈-preserves-∈ x≈y x∈P)

  ∪-preserves-∈ˡ : {P Q : FiniteSet} → {x : D} → x ∈ P → x ∈ P ∪ Q
  ∪-preserves-∈ˡ {ps} {[]} {x} x∈P = x∈P
  ∪-preserves-∈ˡ {ps} {q ∷ qs} {x} x∈P with (q ∈? ps)
  ... | yes _ = ∪-preserves-∈ˡ {Q = qs} x∈P
  ... | no _  = ∪-preserves-∈ˡ {P = q ∷ ps} {Q = qs} (there x∈P)

  ∪-preserves-∈ʳ : {P Q : FiniteSet} → {x : D} → x ∈ Q → x ∈ P ∪ Q
  ∪-preserves-∈ʳ {ps} {q ∷ qs} {x} x∈Q with (q ∈? ps)
  ∪-preserves-∈ʳ {ps} {q ∷ qs} {x} (here x≈q) | yes q∈ps = 
    let
      x∈ps : x ∈ ps
      x∈ps = ≈-preserves-∈ (sym x≈q) q∈ps
    in ∪-preserves-∈ˡ {Q = qs} x∈ps
  ∪-preserves-∈ʳ {ps} {q ∷ qs} {x} (there x∈qs) | yes _ =
    ∪-preserves-∈ʳ {Q = qs} x∈qs
  ∪-preserves-∈ʳ {ps} {q ∷ qs} {x} (here x≈q) | no _ =
    ∪-preserves-∈ˡ{P = q ∷ ps} {Q = qs} (here x≈q)
  ∪-preserves-∈ʳ {ps} {q ∷ qs} {x} (there x∈qs) | no _ =
    ∪-preserves-∈ʳ {P = q ∷ ps} {Q = qs} x∈qs

  ⊎→∪ : {P Q : FiniteSet} → {x : D} → x ∈ P ⊎ x ∈ Q → x ∈ P ∪ Q
  ⊎→∪ (inj₁ x∈P) = ∪-preserves-∈ˡ x∈P
  ⊎→∪ (inj₂ x∈Q) = ∪-preserves-∈ʳ x∈Q

  ∪→⊎ : {P Q : FiniteSet} → {x : D} → x ∈ P ∪ Q → x ∈ P ⊎ x ∈ Q
  ∪→⊎ {P = ps} {Q = []} x∈P∪Q = inj₁ x∈P∪Q
  ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q with q ∈? ps | x ≟ q 
  ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | yes x≈q = inj₂ (here x≈q)
  ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | no _ with (∪→⊎ {P = ps} {Q = qs} x∈P∪Q)
  ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | no _ | inj₁ x∈ps =
    inj₁ x∈ps
  ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | yes q∈ps | no _ | inj₂ x∈qs =
    inj₂ (there x∈qs)
  ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | no _ | yes x≈q = inj₂ (here x≈q)
  ∪→⊎ {P = ps} {Q = q ∷ qs} {x = x} x∈P∪Q | no _ | no _ with (∪→⊎ {P = q ∷ ps} {Q = qs} x∈P∪Q)
  ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | no _ | no ¬x≈q | inj₁ (here x≈q) =
    ⊥-elim (¬x≈q x≈q)
  ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | no _ | no ¬x≈q | inj₁ (there x∈ps) =
    inj₁ x∈ps
  ∪→⊎ {P = ps} {q ∷ qs} {x = x} x∈P∪Q | no _ | no _ | inj₂ x∈qs = inj₂ (there x∈qs)

  ∅⊆P : (P : FiniteSet) → ∅ ⊆ P
  ∅⊆P P = All.[]

  ∈→⊆ : (P : FiniteSet) → (x : D) → x ∈ P → ｛ x ｝ ⊆ P
  ∈→⊆ ps x x∈ps = x∈ps All.∷ All.[]

  ⊆→∈ : (P : FiniteSet) → (x : D) → ｛ x ｝ ⊆ P → x ∈ P
  ⊆→∈ P x (x∈P All.∷ _) = x∈P

  ∈→∈→⊆ : (P Q : FiniteSet) → (∀ (x : D) → x ∈ P → x ∈ Q) → P ⊆ Q
  ∈→∈→⊆ [] qs f = All.[]
  ∈→∈→⊆ (p ∷ ps) qs f = f p (here refl) All.∷ ∈→∈→⊆ ps qs f′
    where f′ : ∀ (x : D) → x ∈ ps → x ∈ qs
          f′ x x∈ps = f x (there x∈ps)

  ⊆→∈→∈ : (P Q : FiniteSet) → P ⊆ Q → (∀ (x : D) → x ∈ P → x ∈ Q)

  ⊆→∈→∈ (p ∷ ps) qs (p∈qs All.∷ ps⊆qs) x (here x≈p) =
    ≈-preserves-∈ (sym x≈p) p∈qs
  ⊆→∈→∈ (p ∷ ps) qs (p∈qs All.∷ ps⊆qs) x (there x∈ps) =
    ⊆→∈→∈ ps qs ps⊆qs x x∈ps

  ∪-commutes′ : (P Q : FiniteSet) → P ∪ Q ⊆ Q ∪ P
  ∪-commutes′ P Q = ∈→∈→⊆ (P ∪ Q) (Q ∪ P) f
    where f : ∀ (x : D) → x ∈ P ∪ Q → x ∈ Q ∪ P
          f x x∈P∪Q with ∪→⊎ x∈P∪Q
          ... | inj₁ x∈P = ∪-preserves-∈ʳ x∈P
          ... | inj₂ x∈Q = ∪-preserves-∈ˡ x∈Q
  ∪-commutes : (P Q : FiniteSet) → P ∪ Q ≐ Q ∪ P
  ∪-commutes P Q = ∪-commutes′ P Q , ∪-commutes′ Q P
  
