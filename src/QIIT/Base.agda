module QIIT.Base where

open import VSet.Prelude
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Nat
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant 
open import Cubical.Categories.Instances.Discrete 
open import Cubical.Categories.Instances.Sets

open Category
open Functor

𝟙 : Category _ _
𝟙 = DiscreteCategory g
  where
    g = ⊤ , isProp→isOfHLevelSuc 2 isPropUnit

LiftCat : {ℓ ℓ' ℓ'' ℓ''' : Level} → Category ℓ ℓ' → Category (ℓ ⊔ ℓ'') (ℓ' ⊔ ℓ''')

C : ℕ → Category _ _
H : (i : ℕ) → Functor (C i) (SET _)

C zero = LiftCat 𝟙
C (suc i) .ob = Σ[ X ∈ C i .ob ] ({!H i .F-ob ?!} → {!SET .ob!})
  where
    w : {!!}
    w = H i .F-ob {!X!}
C (suc i) .Hom[_,_] = {!!}
C (suc i) .Category.id = {!!}
C (suc i) ._⋆_ = {!!}
C (suc i) .⋆IdL = {!!}
C (suc i) .⋆IdR = {!!}
C (suc i) .⋆Assoc = {!!}
C (suc i) .isSetHom = {!!}

H zero = Constant (C zero) (SET _) (⊤ , isProp→isOfHLevelSuc 1 isPropUnit)
H (suc i) = {!!}
