
module VSet.Data.Nat.WellFounded where

open import VSet.Prelude
open import VSet.Data.Nat hiding (_+_; _<_)
open import VSet.Data.Nat.Properties
open import VSet.Data.Fin.Base
open import VSet.Data.SumTree.Base
open import Cubical.Data.Nat.Order
open import Cubical.Induction.WellFounded
open import VSet.Relation.WellFounded.Lex 
open import Cubical.Relation.Binary.Base 

open BinaryRelation

private
  variable
    ℓ ℓ' : Level

accℕ : (A B : ℕ) → B < A → Acc _<_ B
accℕ zero B B<0 = absurd (x≮0 B B<0)
accℕ (suc A) zero _ = acc (λ C C<0 → absurd (x≮0 C C<0))
accℕ (suc A) (suc B) B'<A' =
  acc (λ C C'≤B' → accℕ A C (≤-trans C'≤B' (pred-≤-pred B'<A')))

ℕ-wellFounded : WellFounded _<_
ℕ-wellFounded A = acc (accℕ A)


_≺²_ : Rel (ℕ × ℕ) (ℕ × ℕ) lzero
_≺²_ = ×-Lex _<_ _<_

<-isTrans : isTrans _<_
<-isTrans a b c a<b b<c = <-trans a<b b<c

ℕ²-wellFounded : WellFounded _≺²_ 
ℕ²-wellFounded = ×-wellFounded {<₁-trans = <-isTrans} {<₂-trans = <-isTrans}
                               ℕ-wellFounded ℕ-wellFounded
