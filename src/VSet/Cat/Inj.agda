{-# OPTIONS --lossy-unification #-}

module VSet.Cat.Inj where

open import VSet.Prelude hiding (id; isIso; _×_; pathToIso)
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Functor.Base renaming (Id to F-Id)
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Properties
open import VSet.Cat.Transport
open import VSet.Data.Fin.Base hiding (⟦_⟧)
open import VSet.Data.Fin.Splice 
open import VSet.Data.Fin.Properties
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
open Functor
open NatIso
open NatTrans
open isIso

α-trans :  (─⊗─ ∘F (F-Id ×F ─⊗─ ))
        ≅ᶜ (─⊗─ ∘F ((─⊗─ ×F F-Id) ∘F ×C-assoc InjCat InjCat InjCat))
α-trans = transport→natIso (─⊗─ ∘F (F-Id ×F ─⊗─)) (─⊗─ ∘F (─⊗─ ×F F-Id) ∘F ×C-assoc InjCat InjCat InjCat) F≡G
  where
    F = (─⊗─ ∘F (F-Id ×F ─⊗─ ))
    G = (─⊗─ ∘F ((─⊗─ ×F F-Id) ∘F ×C-assoc InjCat InjCat InjCat))
    obEq : (c : ℕ × ℕ × ℕ)
         → F-ob (─⊗─ ∘F (F-Id ×F ─⊗─)) c
         ≡  F-ob (─⊗─ ∘F (─⊗─ ×F F-Id) ∘F ×C-assoc InjCat InjCat InjCat) c
    obEq (x , y , z) = +-assoc x y z
    homEq : {c c' : ℕ × ℕ × ℕ} → (f : (InjCat ×C InjCat ×C InjCat) [ c , c' ])
          → PathP (λ i → Inj (obEq c i) (obEq c' i)) (F .F-hom f) (G .F-hom f)
    homEq {l , m , n} {l' , m' , n'} (f , g , h) = u
      where
        u : PathP (λ i → Inj (+-assoc l m n i) (+-assoc l' m' n' i))
                  (f ⊕ (g ⊕ h)) ((f ⊕ g) ⊕ h)
        u = transport-filler α-p (f ⊕ (g ⊕ h)) ▷ sym (assoc f g h)
    F≡G : F ≡ G
    F≡G = Functor≡ obEq homEq 

ρ-F-l : Functor InjCat InjCat
ρ-F-l = ─⊗─ ∘F (rinj InjCat InjCat unit)
ρ-F-r : Functor InjCat InjCat
ρ-F-r = F-Id
η-F-r : Functor InjCat InjCat
η-F-r = F-Id
η-F-l : Functor InjCat InjCat
η-F-l = ─⊗─ ∘F (linj InjCat InjCat unit)

ρ-trans :  (─⊗─ ∘F linj InjCat InjCat 0)
        ≅ᶜ F-Id
ρ-trans = transport→natIso (─⊗─ ∘F linj InjCat InjCat 0) F-Id F≡G
  where
    F : Functor InjCat InjCat
    F = (─⊗─ ∘F linj InjCat InjCat 0)
    G : Functor InjCat InjCat
    G = F-Id
    obEq : (c : ℕ) → c + 0 ≡ c
    obEq c = +-zero c
    homEq : {c c' : ℕ} → (f : Inj c c')
          → PathP (λ i → Inj (obEq c i) (obEq c' i)) (F .F-hom f) (G .F-hom f)
    homEq {c} {c'} f = u
      where
        u : PathP (λ i → Inj (+-zero c i) (+-zero c' i)) (f ⊕ 𝟘) f
        u = transport-filler ρ-p (f ⊕ 𝟘) ▷ sym (right-unit f)
    F≡G : F ≡ G
    F≡G = Functor≡ obEq homEq 

η-trans :  (─⊗─ ∘F rinj InjCat InjCat 0)
        ≅ᶜ F-Id
η-trans = transport→natIso (─⊗─ ∘F rinj InjCat InjCat 0) F-Id F≡G
  where
    F : Functor InjCat InjCat
    F = ─⊗─ ∘F rinj InjCat InjCat 0
    G : Functor InjCat InjCat
    G = F-Id
    obEq : (c : ℕ) → 0 + c ≡ c
    obEq c = refl
    homEq : {c c' : ℕ} → (f : Inj c c')
          → PathP (λ i → Inj (obEq c i) (obEq c' i)) (F .F-hom f) (G .F-hom f)
    homEq {c} {c'} f = u
      where
        u : PathP (λ i → Inj c c') (𝟘 ⊕ f) f
        u = transport-filler η-p (𝟘 ⊕ f) ▷ sym (left-unit f)
    F≡G : F ≡ G
    F≡G = Functor≡ obEq homEq 

open MonoidalCategory
open MonoidalStr

InjMonoidalStr : MonoidalStr InjCat
InjMonoidalStr .tenstr = InjTensor
InjMonoidalStr .MonoidalStr.α = α-trans
InjMonoidalStr .MonoidalStr.η = η-trans
InjMonoidalStr .MonoidalStr.ρ = ρ-trans
InjMonoidalStr .pentagon = u
  where
    ti = transportInj
    u : (w x y z : ℕ) →
         ((αInj w x y ⊕ Id) ∘ʲ (αInj w (x + y) z)) ∘ʲ (Id ⊕ αInj  x y z)
         ≡ (αInj (w + x) y z) ∘ʲ (αInj  w x (y + z))
    u w x y z =
      ((αInj w x y ⊕ Id) ∘ʲ αInj w (x + y) z) ∘ʲ (Id ⊕ αInj x y z)
        ≡⟨ cong₂ (λ ○ □ → ((αInj w x y ⊕ ○) ∘ʲ αInj w (x + y) z) ∘ʲ (□ ⊕ αInj x y z))
                          (sym (transportRefl Id)) (sym (transportRefl Id)) ⟩
      ((αInj w x y ⊕ ti refl) ∘ʲ αInj w (x + y) z) ∘ʲ (ti refl ⊕ αInj x y z)
        ≡⟨ cong₂ _∘ʲ_ (cong₂ _∘ʲ_ (transport-⊕-transport (+-assoc w x y) refl ) refl)
                                  (transport-⊕-transport refl (+-assoc x y z)) ⟩
      (transportInj (cong₂ _+_ (+-assoc w x y) refl) ∘ʲ αInj w (x + y) z) ∘ʲ transportInj (cong₂ _+_ refl (+-assoc x y z))
        ≡⟨ cong₂ _∘ʲ_ (transport-∘ʲ-transport (λ i → +-assoc w (x + y) z i) (λ i → +-assoc w x y i + z)) refl ⟩
      transportInj ((λ i → +-assoc w (x + y) z i) ∙ (λ i → +-assoc w x y i + z)) ∘ʲ transportInj (cong₂ _+_ refl (+-assoc x y z))
        ≡⟨ transport-∘ʲ-transport (λ i → w + +-assoc x y z i) ((λ i → +-assoc w (x + y) z i) ∙ (λ i → +-assoc w x y i + z)) ⟩
      transportInj ((λ i → w + +-assoc x y z i) ∙ (λ i → +-assoc w (x + y) z i) ∙ (λ i → +-assoc w x y i + z))
        ≡⟨ cong transportInj (isSetℕ (w + (x + (y + z))) (((w + x) + y) + z) _ _) ⟩
      transportInj ((λ i → +-assoc w x (y + z) i) ∙ (λ i → +-assoc (w + x) y z i))
        ≡⟨ sym (transport-∘ʲ-transport (λ i → +-assoc w x (y + z) i) (λ i → +-assoc (w + x) y z i)) ⟩
      αInj (w + x) y z ∘ʲ αInj w x (y + z) ▯
InjMonoidalStr .triangle x y = w
  where
    u : +-assoc x 0 y ∙ (cong₂ _+_ (+-zero x) (λ _ → y)) ≡ refl
    u = isSetℕ (x + (0 + y)) (x + y) (+-assoc x 0 y ∙ cong₂ _+_ (+-zero x) (λ _ → y)) refl
    w : ((transportInj (+-zero x)) ⊕ (idInj y))
      ∘ʲ (transportInj (+-assoc x 0 y)) 
      ≡ idInj x ⊕ transportInj refl
    w =
      (transportInj (+-zero x) ⊕ idInj y) ∘ʲ transportInj (+-assoc x 0 y)
        ≡⟨ cong (λ ○ → (_ ⊕ ○) ∘ʲ transportInj (+-assoc x 0 y))
                (sym (transportRefl (idInj y))) ⟩
      (transportInj (+-zero x) ⊕ transportInj (λ _ → y)) ∘ʲ transportInj (+-assoc x 0 y)
        ≡⟨ cong₂ _∘ʲ_ (transport-⊕-transport (+-zero x) (λ _ → y)) refl ⟩
      transportInj (cong₂ _+_ (+-zero x) (λ _ → y)) ∘ʲ transportInj (+-assoc x 0 y)
        ≡⟨ transport-∘ʲ-transport (+-assoc x 0 y) (λ i → +-zero x i + y) ⟩
      transportInj (+-assoc x 0 y ∙ (cong₂ _+_ (+-zero x) (λ _ → y)))  
        ≡⟨ cong transportInj u ⟩
      transportInj refl
        ≡⟨ sym (transport-⊕-transport (λ _ → x) (λ _ → 0 + y)) ⟩
      transportInj refl ⊕ transportInj refl
        ≡⟨ cong (_⊕ transportInj refl) ((transportRefl (idInj x))) ⟩
      idInj x ⊕ transportInj refl ▯

InjMonoidalCat : MonoidalCategory ℓ-zero ℓ-zero
InjMonoidalCat .C = InjCat
InjMonoidalCat .monstr = InjMonoidalStr
