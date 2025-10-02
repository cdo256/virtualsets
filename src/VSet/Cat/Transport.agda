{-# OPTIONS --lossy-unification #-}

module VSet.Cat.Transport where

open import VSet.Prelude hiding (id; isIso)
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Functor.Base renaming (Id to F-Id)
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  -- Transport the codomain of identity.
  transportHom : {a b : ob} (p : a ≡ b) → Hom[ a , b ]
  transportHom {a} {b} p = subst (Hom[ a ,_]) p (id {a})

  transportHom-idL
    : {x y z : ob} (p : x ≡ y) (f : Hom[ y , z ])
    → transportHom p ⋆ f ≡ subst2 Hom[_,_] (sym p) refl f
  transportHom-idL {x} {y} {z} = J P r
    where
      P : (y : ob) → x ≡ y → Type ℓ'
      P y q = (f : Hom[ y , z ]) → transportHom q ⋆ f ≡ subst2 Hom[_,_] (sym q) refl f
      r : (f : Hom[ x , z ]) → _ ≡ _
      r f =
        transportHom refl ⋆ f
          ≡⟨ cong (_⋆ f) (transportRefl id) ⟩
        id ⋆ f
          ≡⟨ ⋆IdL f ⟩
        f
          ≡⟨ sym (transportRefl f) ⟩
        transport refl f ▯

  transportHom-idR
    : {x y z : ob} (p : y ≡ z) (f : Hom[ x , y ])
    → f ⋆ transportHom p ≡ subst2 Hom[_,_] refl p f
  transportHom-idR {x} {y} {z} = J P r
    where
      P : (z : ob) → y ≡ z → Type ℓ'
      P z q = (f : Hom[ x , y ]) → f ⋆ transportHom q ≡ subst2 Hom[_,_] refl q f
      r : (f : Hom[ x , y ]) → _ ≡ _
      r f =
        f ⋆ transportHom refl
          ≡⟨ cong (f ⋆_) (transportRefl id) ⟩
        f ⋆ id
          ≡⟨ ⋆IdR f ⟩
        f
          ≡⟨ sym (transportRefl f) ⟩
        transport refl f ▯

  transportHom-cancel
    : {y z : ob} (p : y ≡ z)
    → transportHom (sym p) ⋆ transportHom p  ≡ id
  transportHom-cancel {y} {z} p =
    transportHom (sym p) ⋆ transportHom p
      ≡⟨ transportHom-idR p (transportHom (sym p)) ⟩
    subst2 Hom[_,_] refl p (subst2 Hom[_,_] refl (sym p) id)
      ≡⟨ transportTransport⁻ (cong₂ Hom[_,_] refl p) id ⟩
    id ▯

open Category
open Functor
open NatTrans
open NatIso
open isIso

module TransportNatIso {C : Category ℓC (ℓC' ⊔ ℓC)} {D : Category ℓD (ℓD' ⊔ ℓD)}
                       (F G : Functor C D) (s : F ≡ G) where

  open Category D
    using ()
    renaming (_⋆_ to _⋆ᴰ_; ⋆IdL to ∙IdLᴰ; ⋆IdR to ∙IdRᴰ)

  obPath : {F G : Functor C D} (p : F ≡ G) → (x : C .ob) → F .F-ob x ≡ G .F-ob x
  obPath p = funExt⁻ (cong F-ob p)

  r : (x : C .ob) → F .F-ob x ≡ G .F-ob x
  r = obPath s 

  P : (G' : Functor C D) → F ≡ G' → Type _
  P G' p = 
       {x y : C .ob} (f : C [ x , y ])
     → F .F-hom f ⋆ᴰ transportHom D (obPath p y)
     ≡ transportHom D (obPath p x) ⋆ᴰ G' .F-hom f

  transport→natIso
    : NatIso F G
  transport→natIso .trans .N-ob x = transportHom D (r x) 
  transport→natIso .nIso x .inv = transportHom D (sym (r x))
  transport→natIso .nIso x .sec = transportHom-cancel D (r x)
  transport→natIso .nIso x .ret = transportHom-cancel D (sym (r x))
  transport→natIso .trans .N-hom = 
      J P t s
    where
      t : P F refl
      t f = 
        F .F-hom f ⋆ᴰ transport refl (D .id)
          ≡⟨ cong (F .F-hom f ⋆ᴰ_) (transportRefl (id D)) ⟩
        F .F-hom f ⋆ᴰ (D .id)
          ≡⟨ ∙IdRᴰ (F .F-hom f) ⟩
        F .F-hom f
          ≡⟨ sym (∙IdLᴰ (F .F-hom f)) ⟩
        (D .id) ⋆ᴰ F .F-hom f
          ≡⟨ cong (_⋆ᴰ F .F-hom f) (sym (transportRefl (id D))) ⟩
        transport refl (D .id) ⋆ᴰ F .F-hom f ▯

open TransportNatIso using (transport→natIso)
