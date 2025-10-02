{-# OPTIONS --lossy-unification #-}

module VSet.Cat.Inj where

open import VSet.Prelude hiding (id; isIso)
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Functor.Base renaming (Id to F-Id)
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Properties
open import VSet.Data.Fin.Base 
open import VSet.Data.Fin.Splice 
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Data.Inj.Properties 
open import VSet.Transform.Inj.Elementary.Base
open import VSet.Transform.Inj.Compose.Base
open import VSet.Transform.Inj.Compose.Properties
open import VSet.Transform.Inj.Tensor.Base
open import VSet.Transform.Inj.Tensor.Properties
open import VSet.Transform.Inj.Tensor.Associator 

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' : Level

open Category

InjCat : Category _ _
InjCat = record
  { ob = ℕ
  ; Hom[_,_] = Inj
  ; id = λ {n} → idInj n
  ; _⋆_ = _∘⁻ʲ_
  ; ⋆IdL = ∘ʲ-idR
  ; ⋆IdR = ∘ʲ-idL
  ; ⋆Assoc = λ x y z → ∘ʲ-assoc z y x
  ; isSetHom = isSetInj
  }


InjProdCat : Category _ _
InjProdCat = InjCat ×C InjCat

⊕-ob : InjProdCat .ob → InjCat .ob
⊕-ob (m , n) = m + n

⊕-hom : {x y : InjProdCat .ob} → InjProdCat [ x , y ]
      → InjCat [ ⊕-ob x , ⊕-ob y ]
⊕-hom (f , g) = f ⊕ g

⊕-id : {x : InjProdCat  .ob}
     → ⊕-hom {x = x} {y = x} (InjProdCat .id)
     ≡ InjCat .id {x = ⊕-ob x}
⊕-id {(m , n)} =
  ⊕-hom {x = (m , n)} {y = (m , n)} (InjProdCat .id)
    ≡⟨ refl ⟩
  ⊕-hom {x = (m , n)} {y = (m , n)} (Id , Id)
    ≡⟨ refl ⟩
  Id {m} ⊕ Id {n}
    ≡⟨ Id⊕Id≡Id {m} {n} ⟩
  Id {m + n} ▯

⊕-seq-ext
  : {l l' m m' n n' : ℕ}
  → (f : Inj l m) (f' : Inj l' m')
  → (g : Inj m n) (g' : Inj m' n')
  → (x : Fin (l + l'))
  → apply ((g ∘ʲ f) ⊕ (g' ∘ʲ f')) x
  ≡ apply ((g ⊕ g') ∘ʲ (f ⊕ f')) x
⊕-seq-ext {zero} {l'} {m} {m'} {n} {n'} (nul m) f' g g' x =
  apply ((g ∘ʲ (nul m)) ⊕ (g' ∘ʲ f')) x
    ≡⟨ refl ⟩
  apply ((nul n) ⊕ (g' ∘ʲ f')) x
    ≡⟨ refl ⟩
  apply (shift n (g' ∘ʲ f')) x
    ≡⟨ apply-shift n (g' ∘ʲ f') x ⟩
  fshift n (apply (g' ∘ʲ f') x)
    ≡⟨ cong (fshift n) (sym (apply-apply g' f' x)) ⟩
  fshift n (apply g' (apply f' x))
    ≡⟨ sym (apply-⊕-fshift g g' (apply f' x)) ⟩
  apply (g ⊕ g') (fshift m (apply f' x))
    ≡⟨ cong (apply (g ⊕ g')) (sym (apply-shift m f' x)) ⟩
  apply (g ⊕ g') (apply (shift m f') x)
    ≡⟨ refl ⟩
  apply (g ⊕ g') (apply ((nul m) ⊕ f') x)
    ≡⟨ apply-apply (g ⊕ g') ((nul m) ⊕ f') x ⟩
  apply ((g ⊕ g') ∘ʲ ((nul m) ⊕ f')) x ▯
⊕-seq-ext {suc l} {l'} {suc m} {m'} {suc n} {n'} (inc fzero f) f' (inc c g) g' fzero =
  apply ((inc c g ∘ʲ inc fzero f) ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  apply (inc (apply (inc c g) fzero) g ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  finject n' (apply (inc c g) fzero)
    ≡⟨ refl ⟩
  finject n' c
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) fzero 
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) (apply (inc (finject m' fzero) (f ⊕ f')) fzero)
    ≡⟨ refl ⟩
  apply (inc c g ⊕ g') (apply (inc fzero f ⊕ f') fzero)
    ≡⟨ apply-apply (inc c g ⊕ g') (inc fzero f ⊕ f') fzero ⟩
  apply ((inc c g ⊕ g') ∘ʲ (inc fzero f ⊕ f')) fzero ▯
⊕-seq-ext {suc l} {l'} {suc m} {m'} {suc n} {n'} (inc (fsuc b) f) f' (inc c g) g' fzero =
  apply ((inc c g ∘ʲ inc (fsuc b) f) ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  apply (inc (apply (inc c g) (fsuc b)) g ⊕ (g' ∘ʲ f')) fzero
    ≡⟨ refl ⟩
  finject n' (apply (inc c g) (fsuc b))
    ≡⟨ refl ⟩
  finject n' (fsplice c (apply g b))
    ≡⟨ sym (fsplice-finject-finject c (apply g b)) ⟩
  fsplice (finject n' c) (finject n' (apply g b))
    ≡⟨ cong (fsplice (finject n' c)) (sym (apply-⊕-finject g g' b)) ⟩
  fsplice (finject n' c) (apply (g ⊕ g') (finject m' b))
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) (fsuc (finject m' b))
    ≡⟨ refl ⟩
  apply (inc (finject n' c) (g ⊕ g')) (apply (inc (finject m' (fsuc b)) (f ⊕ f')) fzero)
    ≡⟨ refl ⟩
  apply (inc c g ⊕ g') (apply (inc (fsuc b) f ⊕ f') fzero)
    ≡⟨ apply-apply (inc c g ⊕ g') (inc (fsuc b) f ⊕ f') fzero ⟩
  apply ((inc c g ⊕ g') ∘ʲ (inc (fsuc b) f ⊕ f')) fzero ▯
⊕-seq-ext {suc l} {l'} {suc m} {m'} {suc n} {n'} (inc b f) f' (inc c g) g' (fsuc x) =
  apply ((inc c g ∘ʲ inc b f) ⊕ (g' ∘ʲ f')) (fsuc x)
    ≡⟨ refl ⟩
  apply ((inc (apply (inc c g) b) (remove b (inc c g) ∘ʲ f)) ⊕ (g' ∘ʲ f')) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc (finject n' (apply (inc c g) b)) ((remove b (inc c g) ∘ʲ f) ⊕ (g' ∘ʲ f'))) (fsuc x)
    ≡⟨ refl ⟩
  fsplice (finject n' (apply (inc c g) b)) (apply ((remove b (inc c g) ∘ʲ f) ⊕ (g' ∘ʲ f')) x)
    ≡⟨ {!!} ⟩
  apply (inc (finject n' c) (g ⊕ g')) (apply (inc (finject m' b) (f ⊕ f')) (fsuc x))
    ≡⟨ refl ⟩
  apply (inc c g ⊕ g') (apply (inc b f ⊕ f') (fsuc x))
    ≡⟨ apply-apply (inc c g ⊕ g') (inc b f ⊕ f') (fsuc x) ⟩
  apply ((inc c g ⊕ g') ∘ʲ (inc b f ⊕ f')) (fsuc x) ▯

⊕-seq : {x y z : InjProdCat .ob} (f : InjProdCat [ x , y ]) (g : InjProdCat [ y , z ])
      → ⊕-hom (f ⋆⟨ InjProdCat ⟩ g) ≡ (⊕-hom f) ⋆⟨ InjCat ⟩ (⊕-hom g)
⊕-seq {(l , l')} {(m , m')} {(n , n')} (f , f') (g , g') =
  injExt ((g ∘ʲ f) ⊕ (g' ∘ʲ f'))
         ((g ⊕ g') ∘ʲ (f ⊕ f'))
         (⊕-seq-ext f f' g g')

InjTensor : TensorStr InjCat
InjTensor = record
  { ─⊗─ = record
    { F-ob = ⊕-ob
    ; F-hom = ⊕-hom
    ; F-id = ⊕-id
    ; F-seq = ⊕-seq
    }
  ; unit = 0
  }

open TensorStr InjTensor
open NatIso
open NatTrans
open isIso

η-trans :  (─⊗─ ∘F linj InjCat InjCat 0)
        ≅ᶜ F-Id
η-trans .trans .N-ob x = transportInj (+-zero x)
η-trans .nIso x .inv = transportInj (sym (+-zero x))
η-trans .nIso x .sec = transportInj-cancel (+-zero x)
η-trans .nIso x .ret = transportInj-cancel (sym (+-zero x))
η-trans .trans .N-hom {x = x} {y = y} f = w
  where
    v : subst2 Inj refl (+-zero y) (f ⊕ 𝟘)
      ≡ subst2 Inj (sym (+-zero x)) refl f
    v = {!!}
    w : transportInj (+-zero y) ∘ʲ (f ⊕ 𝟘)
      ≡ f ∘ʲ transportInj (+-zero x) 
    w =
      transportInj (+-zero y) ∘ʲ (f ⊕ 𝟘)
        ≡⟨ transportInj-idR (+-zero y) (f ⊕ 𝟘) ⟩
      subst2 Inj refl (+-zero y) (f ⊕ 𝟘)
        ≡⟨ cong (subst2 Inj refl (+-zero y)) {!!} ⟩
      (subst2 Inj refl (+-zero y) $
       subst2 Inj (sym (+-zero x)) (sym (+-zero y)) f)
        ≡⟨ cong (subst2 Inj refl (+-zero y)) (sym (subst2-stack' Inj (sym (+-zero x)) (sym (+-zero y)) f)) ⟩
      (subst2 Inj refl (+-zero y) $
       subst2 Inj refl (sym (+-zero y)) $
       subst2 Inj (sym (+-zero x)) refl f)
        ≡⟨ transportTransport⁻ (cong₂ Inj refl (+-zero y)) (subst2 Inj (sym (+-zero x)) refl f) ⟩
      subst2 Inj (sym (+-zero x)) refl f
        ≡⟨ sym (transportInj-idL (+-zero x) f) ⟩
      f ∘ʲ transportInj (+-zero x) ▯

α-trans :  (─⊗─ ∘F (F-Id ×F ─⊗─ ))
        ≅ᶜ (─⊗─ ∘F ((─⊗─ ×F F-Id) ∘F ×C-assoc InjCat InjCat InjCat))
α-trans .trans .N-ob (x , y , z) = transportInj (+-assoc x y z)
α-trans .nIso (x , y , z) .inv = transportInj (sym (+-assoc x y z))
α-trans .nIso (x , y , z) .sec = transportInj-cancel (+-assoc x y z)
α-trans .nIso (x , y , z) .ret = transportInj-cancel (sym (+-assoc x y z))
α-trans .trans .N-hom {x = (l , m , n)} {y = (l' , m' , n')} (f , g , h) =
    transportInj (+-assoc l' m' n') ∘ʲ (f ⊕ (g ⊕ h))
      ≡⟨ transportInj-idR (+-assoc l' m' n') (f ⊕ (g ⊕ h)) ⟩
    subst2 Inj refl (+-assoc l' m' n') (f ⊕ (g ⊕ h))
      ≡⟨ sym (transport⁻Transport (cong₂ Inj (+-assoc l m n) refl)
               (subst2 Inj (λ _ → l + (m + n)) (+-assoc l' m' n') (f ⊕ (g ⊕ h)))) ⟩
    subst2 Inj (sym (+-assoc l m n)) refl
     (subst2 Inj (+-assoc l m n) refl
       (subst2 Inj refl (+-assoc l' m' n') (f ⊕ (g ⊕ h))))
      ≡⟨ cong (subst2 Inj (sym (+-assoc l m n)) refl) v ⟩
    subst2 Inj (sym (+-assoc l m n)) refl ((f ⊕ g) ⊕ h)
      ≡⟨ sym (transportInj-idL (+-assoc l m n) ((f ⊕ g) ⊕ h)) ⟩
    ((f ⊕ g) ⊕ h) ∘ʲ transportInj (+-assoc l m n) ▯
  where
  v : (subst2 Inj (+-assoc l m n) refl $
       subst2 Inj refl (+-assoc l' m' n') $
       (f ⊕ (g ⊕ h)))
    ≡ (f ⊕ g) ⊕ h
  v =
    (subst2 Inj (+-assoc l m n) refl $
     subst2 Inj refl (+-assoc l' m' n') $
     f ⊕ (g ⊕ h))
      ≡⟨ subst2-stack Inj (+-assoc l m n) (+-assoc l' m' n') (f ⊕ (g ⊕ h)) ⟩
    subst2 Inj (+-assoc l m n) (+-assoc l' m' n') (f ⊕ (g ⊕ h))
      ≡⟨ sym (assoc f g h) ⟩
    (f ⊕ g) ⊕ h ▯

data InductiveCat (C : Category ℓ ℓ') : Type (ℓ-suc (ℓ ⊔ ℓ')) where
  Cᶜ : InductiveCat C
  _×ᶜ_ : InductiveCat C → InductiveCat C → InductiveCat C

⟦_⟧ᶜ : {C : Category ℓ ℓ'} → InductiveCat C → Category ℓ ℓ'
⟦_⟧ᶜ {C = C} Cᶜ = C
⟦ C ×ᶜ D ⟧ᶜ = ⟦ C ⟧ᶜ ×C ⟦ D ⟧ᶜ
data InductiveFunctor (Base : Category ℓ ℓ') (_⊗_ : Functor (Base ×C Base) Base) : (C D : InductiveCat Base) → Type (ℓ-suc (ℓ ⊔ ℓ')) where
  Idꟳ : (C : InductiveCat Base) → InductiveFunctor Base _⊗_ C C
  Constantꟳ : (C D : InductiveCat Base) (x : ⟦ D ⟧ᶜ .ob) → InductiveFunctor Base _⊗_ C D
  _×ꟳ_ : {C C' D D' : InductiveCat Base} (F : InductiveFunctor Base _⊗_ C D) (G : InductiveFunctor Base _⊗_ C' D')
       → InductiveFunctor Base _⊗_ (C ×ᶜ C') (D ×ᶜ D')
  _⊗ꟳ_ : {C D : InductiveCat Base} (F : InductiveFunctor Base _⊗_ C Cᶜ) (G : InductiveFunctor Base _⊗_ D Cᶜ)
       → InductiveFunctor Base _⊗_ (C ×ᶜ D) Cᶜ

-- data InductiveFunctor ℓo ℓh ℓo' ℓh' : Category ℓo ℓh → Category ℓo' ℓh' → Type (ℓ-suc (ℓo ⊔ ℓh ⊔ ℓo' ⊔ ℓh')) where
--     Idꟳ : (C : Category ℓo ℓh) → InductiveFunctor ℓo ℓh ℓo ℓh C C
--     Constantꟳ : (C D : Category ℓ ℓ') (x : D .ob) → InductiveFunctor C D
--     _×ꟳ_ : {C C' D D' : Category ℓ ℓ'} (F : InductiveFunctor C D) (G : InductiveFunctor C' D') → InductiveFunctor (C ×C C') (D ×C D')
--     _⊕ꟳ_ : {C D : Category ℓ ℓ'} (F : InductiveFunctor C InjCat) (G : InductiveFunctor D InjCat)
--          → InductiveFunctor (C ×C D) InjCat

-- Shouldn't be difficult to check, but Agda struggles to check performantly.
{-# TERMINATING #-}
⟦_⟧ꟳ : {Base : Category ℓ ℓ'} {_⊗_ : Functor (Base ×C Base) Base} {C D : InductiveCat Base}
     → InductiveFunctor Base _⊗_ C D → Functor ⟦ C ⟧ᶜ ⟦ D ⟧ᶜ
⟦ Idꟳ C ⟧ꟳ = F-Id
⟦ Constantꟳ C D x ⟧ꟳ = Constant ⟦ C ⟧ᶜ ⟦ D ⟧ᶜ x
⟦ F ×ꟳ G ⟧ꟳ = ⟦ F ⟧ꟳ ×F ⟦ G ⟧ꟳ
⟦_⟧ꟳ {_⊗_ = _⊗_} (F ⊗ꟳ G) = _⊗_ ∘F (⟦ F ⟧ꟳ ×F ⟦ G ⟧ꟳ)

⟦_⟧ꟳ⁺ : {C D : InductiveCat InjCat}
      → InductiveFunctor InjCat ─⊗─ C D → Functor ⟦ C ⟧ᶜ ⟦ D ⟧ᶜ
⟦ F ⟧ꟳ⁺ = ⟦_⟧ꟳ {Base = InjCat} {_⊗_ = ─⊗─} F

η-F-l : Functor InjCat InjCat
η-F-l = ─⊗─ ∘F (rinj InjCat InjCat unit)
η-F-r : Functor InjCat InjCat
η-F-r = F-Id
ρ-F-r : Functor InjCat InjCat
ρ-F-r = F-Id
ρ-F-l : Functor InjCat InjCat
ρ-F-l = ─⊗─ ∘F (linj InjCat InjCat unit)

-- transport→NatIso : (F G : Functor InjCat InjCat) → NatIso F G

open MonoidalCategory
open MonoidalStr

InjMonoidalStr : MonoidalStr InjCat
InjMonoidalStr .tenstr = InjTensor
InjMonoidalStr .MonoidalStr.α = α-trans
InjMonoidalStr .MonoidalStr.η = {!!}
InjMonoidalStr .MonoidalStr.ρ = {!!}
InjMonoidalStr .pentagon = {!!}
InjMonoidalStr .triangle = {!!}

InjMonoidalCat' : MonoidalCategory ℓ-zero ℓ-zero
InjMonoidalCat' .C = InjCat
InjMonoidalCat' .monstr = {!!}

-- InjMonoidalCat : MonoidalCategory ℓ-zero ℓ-zero
-- InjMonoidalCat = record
--   { C = InjCat
--   ; monstr = record
--     { tenstr = InjTensor
--     ; α = α
--     ; η = record
--       { trans = record
--         { N-ob = idInj
--         ; N-hom = η-hom
--         }
--       ; nIso = η-iso
--       }
--     ; ρ = record
--       { trans = record
--         { N-ob = ρ-ob
--         ; N-hom = ρ-hom
--         }
--       ; nIso = ρ-iso
--       }
--     ; pentagon = {!!}
--     ; triangle = {!!}
--     }
--   }
--   where
--     η-ob : (x : ℕ) → Inj (x + 0) x 
--     η-ob zero = nul 0
--     η-ob (suc n) = inc f0 (η-ob n)
--     η-hom : N-hom-Type (─⊗─ ∘F rinj InjCat InjCat 0) F-Id idInj 
--     η-hom {zero} {y} (nul y) = refl
--     η-hom {suc x} {suc y} (inc b f) =
--       (idInj (suc y) ∘ʲ (nul zero ⊕ inc b f))
--         ≡⟨ refl ⟩
--       idInj (suc y) ∘ʲ inc b f
--         ≡⟨ ∘ʲ-idL (inc b f) ⟩
--       inc b f
--         ≡⟨ sym (∘ʲ-idR (inc b f)) ⟩
--       inc b f ∘ʲ idInj (suc x) ▯
--     η-iso : (x : ℕ) → isIso InjCat (idInj x)
--     η-iso zero = isiso (nul 0) refl refl
--     η-iso (suc x) = isiso (idInj (suc x)) Id⊕Id≡Id Id⊕Id≡Id
--     ρ-ob : (x : ℕ) → Inj (x + 0) x 
--     ρ-ob zero = nul zero
--     ρ-ob (suc x) = inc f0 (ρ-ob x)
--     ρ⁻¹-ob : (x : ℕ) → Inj x (x + 0)
--     ρ⁻¹-ob zero = nul 0
--     ρ⁻¹-ob (suc x) = inc f0 (ρ⁻¹-ob x)
--     ρ-hom : N-hom-Type (─⊗─ ∘F linj InjCat InjCat unit) 𝟙⟨ InjCat ⟩ ρ-ob
--     ρ-hom {zero} {y} (nul y) =
--       ρ-ob y ∘ʲ ((─⊗─ ∘F linj InjCat InjCat unit) .Functor.F-hom (nul y))
--         ≡⟨ refl ⟩
--       ρ-ob y ∘ʲ ((─⊗─ ∘F (F-Id ,F Constant InjCat InjCat unit)) .Functor.F-hom (nul y))
--         ≡⟨ refl ⟩
--       ρ-ob y ∘ʲ (nul y ⊕ nul 0)
--         ≡⟨ refl ⟩
--       ρ-ob y ∘ʲ (shift y (nul 0))
--         ≡⟨ cong (ρ-ob y ∘ʲ_) (shift-nul 0 y) ⟩
--       ρ-ob y ∘ʲ (nul (y + 0))
--         ≡⟨ refl ⟩
--       nul y ∘ʲ nul zero ▯
--     ρ-hom {suc x} {suc y} (inc fzero f) =
--       ρ-ob (suc y) ∘ʲ ((─⊗─ ∘F linj InjCat InjCat unit) .Functor.F-hom (inc fzero f))
--         ≡⟨ refl ⟩
--       ρ-ob (suc y) ∘ʲ (inc fzero f ⊕ nul 0)
--         ≡⟨ refl ⟩
--       inc f0 (ρ-ob y) ∘ʲ (inc (finject 0 fzero) (f ⊕ nul 0))
--         ≡⟨ refl ⟩
--       inc (apply (inc f0 (ρ-ob y)) fzero)
--           (remove fzero (inc f0 (ρ-ob y)) ∘ʲ (f ⊕ nul 0))
--         ≡⟨ refl ⟩
--       inc fzero (ρ-ob y ∘ʲ (f ⊕ nul 0))
--         ≡⟨ cong (inc fzero) {!!} ⟩
--       inc fzero (f ∘ʲ ρ-ob x)
--         ≡⟨ refl ⟩
--       inc fzero f ∘ʲ inc f0 (ρ-ob x) ▯
--     ρ-hom {suc x} {suc y} (inc (fsuc b) f) =
--       ρ-ob (suc y) ∘ʲ ((─⊗─ ∘F linj InjCat InjCat unit) .Functor.F-hom (inc (fsuc b) f))
--         ≡⟨ refl ⟩
--       ρ-ob (suc y) ∘ʲ (inc (fsuc b) f ⊕ nul 0)
--         ≡⟨ refl ⟩
--       inc f0 (ρ-ob y) ∘ʲ (inc (finject 0 (fsuc b)) (f ⊕ nul 0))
--         ≡⟨ refl ⟩
--       inc (apply (inc f0 (ρ-ob y)) (fsuc (finject 0 b)))
--           (remove (fsuc (finject 0 b)) (inc f0 (ρ-ob y)) ∘ʲ (f ⊕ nul 0))
--         ≡⟨ refl ⟩
--       inc (fsuc (apply (ρ-ob y) (finject 0 b)))
--           (remove (fsuc (finject 0 b)) (inc f0 (ρ-ob y)) ∘ʲ (f ⊕ nul 0))
--         ≡⟨ cong₂ inc (ρ-apply (suc y) (fsuc b)) {!!} ⟩
--       inc (fsuc b) (f ∘ʲ ρ-ob x)
--         ≡⟨ refl ⟩
--       inc (fsuc b) f ∘ʲ inc f0 (ρ-ob x) ▯
--       where
--         ρ-apply : (y : ℕ) (b : Fin y) → (apply (ρ-ob y) (finject 0 b)) ≡ b
--         ρ-apply y fzero = refl
--         ρ-apply (suc y) (fsuc b) =
--           cong fsuc (ρ-apply y b)
--     ρ-iso-sect : (x : ℕ) → ρ-ob x ∘ʲ ρ⁻¹-ob x ≡ idInj x
--     ρ-iso-sect zero = refl
--     ρ-iso-sect (suc x) =
--       inc f0 (ρ-ob x) ∘ʲ inc f0 (ρ⁻¹-ob x)
--         ≡⟨ refl ⟩
--       inc f0 (remove f0 (inc f0 ( ρ-ob x)) ∘ʲ ρ⁻¹-ob x)
--         ≡⟨ refl ⟩
--       inc f0 (ρ-ob x ∘ʲ ρ⁻¹-ob x)
--         ≡⟨ cong (inc f0) (ρ-iso-sect x) ⟩
--       inc f0 (idInj x) ▯
--     ρ-iso-retr : (x : ℕ) → ρ⁻¹-ob x ∘ʲ ρ-ob x ≡ idInj (x + 0)
--     ρ-iso-retr zero = refl
--     ρ-iso-retr (suc x) =
--       inc f0 (ρ⁻¹-ob x) ∘ʲ inc f0 (ρ-ob x)
--         ≡⟨ refl ⟩
--       inc f0 (remove f0 (inc f0 (ρ⁻¹-ob x)) ∘ʲ ρ-ob x)
--         ≡⟨ refl ⟩
--       inc f0 (ρ⁻¹-ob x ∘ʲ ρ-ob x)
--         ≡⟨ cong (inc f0) (ρ-iso-retr x) ⟩
--       inc f0 (idInj (x + 0)) ▯
--     ρ-iso : (x : ℕ) → isIso InjCat (ρ-ob x)
--     ρ-iso x = isiso (ρ⁻¹-ob x) (ρ-iso-sect x) (ρ-iso-retr x)
