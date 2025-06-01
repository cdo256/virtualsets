module FinSetoid.Base where

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
  ... | no z = x ∷ (P ∪ Q)
  
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
