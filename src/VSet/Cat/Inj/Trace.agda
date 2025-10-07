module VSet.Cat.Inj.Trace where

open import Cubical.Categories.Category
-- open import Cubical.Categories.Constructions.BinProduct
-- open import Cubical.Categories.Functor.Base renaming (Id to F-Id)
-- open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Monoidal
-- open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Data.Nat
-- open import Cubical.Data.Nat.Properties
-- open import Cubical.Data.Sigma
open import VSet.Cat.Trace
open import VSet.Cat.Inj.Base
open import VSet.Cat.Inj.Monoidal
open import VSet.Cat.Transport
open import VSet.Data.Fin.Base hiding (⟦_⟧; pred)
-- open import VSet.Data.Fin.Properties
-- open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
-- open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Prelude hiding (id; isIso; _×_; pathToIso)
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Compose.Properties
-- open import VSet.Transform.Inj.Elementary.Base
open import VSet.Transform.Inj.Tensor.Associator 
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Trace.Base
open import VSet.Transform.Inj.Trace.Properties
-- open import VSet.Transform.Inj.Tensor.Properties

open LeftTrace
open MonoidalCategory InjMonoidalCat

LeftTraceInj : LeftTrace InjMonoidalCat
LeftTraceInj .ltrace = trace
LeftTraceInj .lvanishing = refl
LeftTraceInj .lvanishing₂ A B X zero f =
  trace X
   (trace 0
    (α⁻¹⟨ 0 , X , B ⟩ ∘ʲ (f ∘ʲ α⟨ 0 , X , A ⟩)))
    ≡⟨ cong (trace X) w ⟩
  trace X f ▯
  where
    w : trace 0 (α⁻¹⟨ 0 , X , B ⟩ ∘ʲ (f ∘ʲ α⟨ 0 , X , A ⟩)) ≡ f
    w =
      α⁻¹⟨ 0 , X , B ⟩ ∘ʲ (f ∘ʲ α⟨ 0 , X , A ⟩)
        ≡⟨ refl ⟩
      transportInj refl ∘ʲ (f ∘ʲ transportInj refl)
        ≡⟨ cong₂ _∘ʲ_ transportInj-refl (cong₂ _∘ʲ_ refl transportInj-refl) ⟩
      Id ∘ʲ (f ∘ʲ Id)
        ≡⟨ cong (Id ∘ʲ_) (∘ʲ-idR f) ⟩
      Id ∘ʲ f
        ≡⟨ ∘ʲ-idL f ⟩
      f ▯
LeftTraceInj .lvanishing₂ A B X (suc Y) f =
  trace X
   (trace (suc Y)
    (α⁻¹⟨ suc Y , X , B ⟩ ∘ʲ (f ∘ʲ α⟨ suc Y , X , A ⟩)))
    ≡⟨ refl ⟩
  trace X
   (trace Y
    (pred (α⁻¹⟨ suc Y , X , B ⟩ ∘ʲ (f ∘ʲ α⟨ suc Y , X , A ⟩))))
    ≡⟨ cong (λ ○ → trace X (trace Y (pred ○))) u ⟩
  trace X
   (trace Y
    (pred (transport (sym (α-p {l = suc Y} {l' = suc Y})) f)))
    ≡⟨ cong (λ ○ → trace X (trace Y ○))
            (sym (subst-pred-reorder (sym (+-assoc Y X A)) (sym (+-assoc Y X B)) f)) ⟩
  trace X
   (trace Y
    (transport (sym (α-p {l = Y} {l' = Y})) (pred f)))
    ≡⟨ cong (λ ○ → trace X (trace Y ○))
            (sym (transportInj-idRL (+-assoc Y X A) (sym (+-assoc Y X B)) (pred f))) ⟩
  trace X
   (trace Y
    (α⁻¹⟨ Y , X , B ⟩ ∘ʲ pred f ∘ʲ α⟨ Y , X , A ⟩))
    ≡⟨ LeftTraceInj .lvanishing₂ A B X Y (pred f) ⟩
  trace (Y + X) (pred f)
    ≡⟨ refl ⟩
  trace (suc Y + X) f ▯
  where
    u : α⁻¹⟨ suc Y , X , B ⟩ ∘ʲ (f ∘ʲ α⟨ suc Y , X , A ⟩)
      ≡ transport (sym (α-p {l = suc Y} {l' = suc Y})) f
    u = transportInj-idRL (+-assoc (suc Y) X A) (sym (+-assoc (suc Y) X B)) f
LeftTraceInj .lsuperposing = {!!}
LeftTraceInj .lsliding = {!!}
LeftTraceInj .ltightening = {!!}
LeftTraceInj .lstrength = {!!}
