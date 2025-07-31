module VSet.Data.InductiveInj.Tests where

open import VSet.Prelude hiding (_∘_)
open import VSet.Data.InductiveInj.Base
open import Cubical.Data.List.Base
open import Cubical.Data.Nat.Base
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Splice
open import VSet.Data.InductiveInj.Base
open import VSet.Data.InductiveInj.Order
open import VSet.Data.InductiveInj.Inverse
open import VSet.Data.InductiveInj.Properties

_ : to-list (cycle-r 3) ≡ f1 ∷ f2 ∷ f3 ∷ f0 ∷ []
_ = refl

_ : to-list (cycle-l 3) ≡ f3 ∷ f0 ∷ f1 ∷ f2 ∷ []
_ = refl

_ : to-list (idInj 4) ≡ f0 ∷ f1 ∷ f2 ∷ f3 ∷ []
_ = refl

_ : apply (idInj 5) f3 ≡ f3 
_ = refl

_ : to-list cross ≡ f1 ∷ f0 ∷ []
_ = refl

_ : apply cross f0 ≡ f1
_ = refl

_ : apply cross f1 ≡ f0
_ = refl

_ : to-list (nul 0) ≡ []
_ = refl

_ : to-list (cycle-r 4) ≡ f1 ∷ f2 ∷ f3 ∷ f4 ∷ f0 ∷ []
_ = refl

_ : to-list (insert f2 f5 (cycle-r 4)) ≡ f1 ∷ f2 ∷ f5 ∷ f3 ∷ f4 ∷ f0 ∷ []
_ = refl

_ : to-list (insert f2 f1 (idInj 4)) ≡ f0 ∷ f2 ∷ f1 ∷ f3 ∷ f4 ∷ []
_ = refl

_ : insert f2 f1 cross ≡ (inc f2 $ inc f0 $ inc f0 $ nul 0)
_ = insert f2 f1 cross ≡⟨ refl ⟩
    insert f2 f1 (inc f1 (inc f0 (nul 0))) ≡⟨ refl ⟩
    inc f2 (insert f1 f1 (inc f0 (nul 0))) ≡⟨ refl ⟩
    inc f2 (inc f0 (insert f0 f0 (nul 0))) ≡⟨ refl ⟩
    inc f2 (inc f0 (inc f0 (nul 0))) ▯

_ : to-list (insert f2 f1 cross) ≡ f2 ∷ f0 ∷ f1 ∷ []
_ = refl

_ : to-list (insert f2 f1 (cycle-r 4)) ≡ f2 ∷ f3 ∷ f1 ∷ f4 ∷ f5 ∷ f0 ∷ []
_ = refl

_ : to-list (insert f1 f0 (idInj 1)) ≡ f1 ∷ f0 ∷ []
_ = refl

_ : to-list (insert f2 f0 (idInj 2)) ≡ f1 ∷ f2 ∷ f0 ∷ []
_ = refl

_ : insert f2 f0 cross ≡ (inc f2 $ inc f1 $ inc f0 $ nul 0)
_ = insert f2 f0 cross ≡⟨ refl ⟩
    (insert f2 f0 $ inc f1 $ inc f0 $ nul 0) ≡⟨ refl ⟩
    (inc f2 $ insert f1 f0 $ inc f0 $ nul 0) ≡⟨ refl ⟩
    (inc f2 $ inc f1 $ insert f0 f0 $ nul 0) ≡⟨ refl ⟩
    (inc f2 $ inc f1 $ inc f0 $ nul 0) ▯

_ : to-list (inv (cycle-r 3)) ≡ f3 ∷ f0 ∷ f1 ∷ f2 ∷ []
_ = refl

_ : to-list (inv (cycle-l 3)) ≡ f1 ∷ f2 ∷ f3 ∷ f0 ∷ []
_ = refl

_ : idInj 2 ∘ʲ cross ≡ cross
_ = refl

_ : cross ∘ʲ idInj 2 ≡ cross
_ = refl

_ : to-list (cross ∘ʲ cross) ≡ to-list (idInj 2)
_ = refl

_ : to-list (shift 1 (idInj 2)) ≡ f1 ∷ f2 ∷ []
_ = refl

_ : to-list (idInj 1 ⊕ idInj 2) ≡ f0 ∷ f1 ∷ f2 ∷ []
_ = refl

_ : to-list (nul 1 ⊕ cycle-l 4) ≡ f5 ∷ f1 ∷ f2 ∷ f3 ∷ f4 ∷ []
_ = refl

_ : to-list (nul 1 ⊕ idInj 1) ≡ f1 ∷ []
_ = refl

g1 : Inj 2 3
g1 = (inc f2 $ inc f0 $ nul 1) 

_ : (inc f3 $ inc f1 $ inc f0 $ nul 1) ≡ insert f2 f0 g1
_ = refl

_ : apply (insert f2 f0 g1) f2 ≡ f0
_ = refl

_ : apply (insert f0 f2 (idInj 2)) f1 ≡ fsplice f2 (apply (idInj 2) (antisplice f0 f1))
_ = refl

_ : apply (insert f0 f2 (idInj 2)) f2 ≡ fsplice f2 (apply (idInj 2) (antisplice f0 f2))
_ = refl

_ : apply (insert f0 f2 (idInj 2)) f2 ≡ fsplice f2 (apply (idInj 2) (antisplice f0 f2))
_ = refl

_ : apply (insert f1 f0 (idInj 2)) f0 ≡ fsplice f0 (apply (idInj 2) (antisplice f1 f0))
_ = refl

_ : apply (insert f1 f0 (idInj 2)) f1 ≡ f0
_ = refl

_ : apply (insert f1 f0 (idInj 2)) f2 ≡ fsplice f0 (apply (idInj 2) (antisplice f1 f2))
_ = refl

_ : apply (insert f1 f2 cross) f1 ≡ f2
_ = refl

_ : apply (insert f1 f2 cross) f0 ≡ fsplice f2 (apply cross (antisplice f1 f0))
_ = refl

_ : apply (insert f1 f2 cross) f2 ≡ fsplice f2 (apply cross (antisplice f1 f2))
_ = refl

-- (1 2 4 0)
g2 : Inj 4 5
g2 = (inc f1 $ inc f1 $ inc f2 $ inc f0 $ nul 1)

_ : insert f1 f3 g2 ≡ (inc f1 $ inc f2 $ inc f1 $ inc f2 $ inc f0 $ nul 1)
_ = refl

_ : to-list (insert f1 f3 g2) ≡ f1 ∷ f3 ∷ f2 ∷ f5 ∷ f0 ∷ []
_ = refl

_ : apply (insert f1 f3 g2) f2 ≡ fsplice f3 (apply g2 (antisplice f1 f2))
_ = refl

_ : apply (insert f4 f3 g2) f2 ≡ fsplice f3 (apply g2 (antisplice f4 f2))
_ = refl
