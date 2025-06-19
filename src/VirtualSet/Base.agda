module VirtualSet.Base where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Fin
  using (Fin) renaming (suc to s; zero to z)
open import Data.Fin.Properties
  using (_≟_; 0≢1+n; suc-injective)
open import Data.Nat
  using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product
  using (Σ; Σ-syntax; _×_; proj₁; proj₂)
open import Data.Product.Base as Product
  using (∃; _×_; _,_)
open import Data.Sum
  using (inj₁; inj₂; _⊎_)
open import Level
  using (_⊔_; 0ℓ) renaming (suc to lsuc)
open import Relation.Binary.Structures
  using (IsEquivalence)
import Relation.Binary.PropositionalEquality.Core as ≡
  using (refl; sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_)
open import Relation.Binary.Reasoning.Syntax
  using (module ≡-syntax)
open import Relation.Nullary.Decidable as Dec
  using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality
  using (inspect; [_])
open import Function.Base
  using (_∘_)
open import Function.Bundles
  using (_↣_; _↔_)


open ≡-Reasoning
private
  variable
    c ℓ : Level.Level



injective : {X Y : Set} → (f : X → Y) → Set
injective {X} {Y} f = ∀ (a b : X) → f a ≡ f b → a ≡ b

add : {x : ℕ} → (a : Fin (ℕ.suc x)) → (b : Fin x) → (Σ[ c ∈ Fin (ℕ.suc x) ] a ≢ c)
add {ℕ.suc x} z b = s b , λ ()
add {ℕ.suc x} (s a) z = z , λ ()
add {ℕ.suc x} (s a) (s b) =
  let
    (c , a≢c) = add a b
  in s (proj₁ (add a b)) , λ a'≡c' → a≢c (suc-injective a'≡c')

del : {x : ℕ} → (a : Fin (ℕ.suc x)) → (Σ[ b ∈ Fin (ℕ.suc x) ] a ≢ b) → Fin x
del {ℕ.zero} z (z , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} z (z , 0≢0) = ⊥-elim (0≢0 ≡.refl)
del {ℕ.suc x} z (s b , a≢b) = b
del {ℕ.suc x} (s a) (z , a≢b) = z
del {ℕ.suc x} (s a) (s b , a'≢b') =
  s (del {x} a (b , λ a≡b → ⊥-elim (a'≢b' (≡.cong s a≡b))))

del-zero-suc : ∀ {x} (b : Fin x) (a≢b : z ≢ s b) → del z (s b , a≢b) ≡ b
del-zero-suc b a≢b with del z (s b , a≢b) | inspect (del z) (s b , a≢b)
... | z | [ eq ] = ≡.sym eq
... | s X | [ eq ] = ≡.sym eq

del-inj : {x : ℕ} → (a : Fin (ℕ.suc x))
        → (B₁ B₂ : Σ[ b ∈ Fin (ℕ.suc x) ] a ≢ b)
        → del a B₁ ≡ del a B₂
        → proj₁ B₁ ≡ proj₁ B₂
del-inj z (z , a≢b₁) (z , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj z (z , a≢b₁) (s b₂ , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₁ ≡.refl)
del-inj z (s b₁ , a≢b₁) (z , a≢b₂) b₁'≡b₂' =
  ⊥-elim (a≢b₂ ≡.refl)
del-inj z (s b₁ , a≢b₁) (s b₂ , a≢b₂) b₁'≡b₂' =
  let b₁' = del z (s b₁ , a≢b₁)
      b₂' = del z (s b₂ , a≢b₂)
      b₁'≡b₁ : b₁' ≡ b₁
      b₁'≡b₁ = del-zero-suc b₁ a≢b₁
      b₂'≡b₂ : b₂' ≡ b₂
      b₂'≡b₂ = del-zero-suc b₂ a≢b₂
  in begin
      s b₁
    ≡⟨ ≡.cong s (≡.sym b₁'≡b₁) ⟩
      s b₁'
    ≡⟨ ≡.cong s b₁'≡b₂' ⟩
      s b₂'
    ≡⟨ ≡.cong s b₂'≡b₂ ⟩
      s b₂ ∎
del-inj (s a) (z , a≢b₁) (z , a≢b₂) b₁'≡b₂' = ≡.refl
del-inj (s a) (z , a≢b₁) (s b₂ , a≢b₂) b₁'≡b₂'
  with del (s a) (z , a≢b₁) | inspect (del (s a)) (z , a≢b₁) | del (s a) (s b₂  , a≢b₂) | inspect (del (s a)) (s b₂ , a≢b₂)
... | z | [ eq₁ ] | z | ()
... | z | _ | s _ | _ = ⊥-elim (0≢1+n b₁'≡b₂')
... | s X | () | _ | _
del-inj (s a) (s b₁ , a≢b₁) (z , a≢b₂) b₁'≡b₂' =
  ≡.sym (del-inj (s a) (z , a≢b₂) (s b₁ , a≢b₁) (≡.sym b₁'≡b₂'))
del-inj (s a) (s b₁ , sa≢sb₁) (s b₂ , sa≢sb₂) b₁'≡b₂'
  with del (s a) (s b₁ , sa≢sb₁) | inspect (del (s a)) (s b₁ , sa≢sb₁) | del (s a) (s b₂  , sa≢sb₂) | inspect (del (s a)) (s b₂ , sa≢sb₂) | b₁'≡b₂'
... | s c₁ | [ eq₁ ] | s c₂ | [ eq₂ ] | _ =
  ≡.cong s (del-inj a (b₁ , λ a≡b₁ → sa≢sb₁ (≡.cong s a≡b₁))
                      (b₂ , λ a≡b₂ → sa≢sb₂ (≡.cong s a≡b₂))
                      (suc-injective b₁'≡b₂'))

add-inj : {x : ℕ} → (a : Fin (ℕ.suc x))
        → (b₁ b₂ : Fin x)
        → proj₁ (add a b₁) ≡ proj₁ (add a b₂)
        → b₁ ≡ b₂
add-inj z z z c₁≡c₂ = ≡.refl
add-inj z (s b₁) (s b₂) c₁≡c₂
  with add z b₁ | inspect (add z) b₁ | add z b₂ | inspect (add z) b₂
... | c₁ , z≢c₁ | [ eq₁ ] | c₂ , z≢c₂ | [ eq₂ ] = suc-injective c₁≡c₂
add-inj (s a) z z c₁≡c₂ = ≡.refl
add-inj (s a) (s b₁) (s b₂) c₁≡c₂
  with add (s a) (s b₁) | inspect (add (s a)) (s b₁) | add (s a) (s b₂) | inspect (add (s a)) (s b₂)
... | s c₁ , sa≢sc₁ | [ eq₁ ] | s c₂ , sa≢sc₂ | [ eq₂ ] =
  ≡.cong s (add-inj a b₁ b₂ (suc-injective c₁≡c₂))

module _ {x y : ℕ} (f : Fin (ℕ.suc x) → Fin (ℕ.suc y)) (inj : injective f) where

  f' : Fin x → Fin y
  f' i =
    let (j , 0≢j) = add z i 
    in del (f z) (f j , λ f0≡fj → 0≢j (inj z j f0≡fj))

  comp : (ai : (b₁ b₂ : Fin x) → proj₁ (add z b₁) ≡ proj₁ (add z b₂) → b₁ ≡ b₂)
       → (di : (B₁ B₂ : Σ[ b ∈ Fin (ℕ.suc y) ] f z ≢ b)
             → del (f z) B₁ ≡ del (f z) B₂ → proj₁ B₁ ≡ proj₁ B₂)
       → injective f'
  comp ai di b₁ b₂ f'b₁≡f'b₂ =
    let
      (c₁ , z≢c₁) = add z b₁
      (c₂ , z≢c₂) = add z b₂
    in
    ai b₁ b₂
       (inj c₁ c₂
            (di (f c₁ , λ fz≡fc₁ → z≢c₁ (inj z c₁ fz≡fc₁))
                (f c₂ , λ fz≡fc₂ → z≢c₂ (inj z c₂ fz≡fc₂))
                f'b₁≡f'b₂))

  sub : Σ[ f' ∈ (Fin x → Fin y) ] injective f'
  sub = f' , comp (add-inj z) (del-inj (f z))

infix 5 ⟦_⟧
infix 10 _!_$_
infix 80 SFin_

SomeFin : Set
SomeFin = ℕ

_+_ : SomeFin → SomeFin → SomeFin
X + Y = X +ℕ Y

+→⊎ : (X Y : SomeFin) → Fin (X + Y) → (Fin X ⊎ Fin Y)
+→⊎ ℕ.zero Y w = inj₂ w
+→⊎ (ℕ.suc X) Y z = inj₁ z
+→⊎ (ℕ.suc X) Y (s w) with +→⊎ X Y w
... | inj₁ a = inj₁ (s a)
... | inj₂ b = inj₂ b

⊎→+ : (X Y : SomeFin) → (Fin X ⊎ Fin Y) → Fin (X + Y)
⊎→+ ℕ.zero Y (inj₂ w) = w
⊎→+ (ℕ.suc X) Y (inj₁ z) = z
⊎→+ (ℕ.suc X) Y (inj₁ (s a)) =
  s (⊎→+ X Y (inj₁ a)) 
⊎→+ (ℕ.suc X) Y (inj₂ b) = 
  s (⊎→+ X Y (inj₂ b)) 

{- I was able to make it work and I'm now stuck on showing that two functions are inverses of eachother. 
The funciton below is meant to show that ⊎→+ X Y ∘ +→⊎ X Y = id, although it's represented a little differently in the standard library:

Inverseˡ : (A → B) → (B → A) → Set _
Inverseˡ f g = ∀ {x y} → y ≈₁ g x → f y ≈₂ x

Inverseʳ : (A → B) → (B → A) → Set _
Inverseʳ f g = ∀ {x y} → y ≈₂ f x → g y ≈₁ x

Inverseᵇ : (A → B) → (B → A) → Set _
Inverseᵇ f g = Inverseˡ f g × Inverseʳ f g

I have used the inspect pattern below to try to rewrite the functions so I can use the recursive case, but I don't quite seem to get there.
The specific case I'm on should be impossible, but I can't find the contradiction in the assumptions.

Goal: +→⊎ (ℕ.suc X) Y z₂ ≡ inj₁ (s E)
————————————————————————————————————————————————————————————
eq  : z₂ ≡ s (⊎→+ X Y (inj₁ E))
E   : Fin X
eq₂ : ⊎→+ (ℕ.suc X) Y z₁ ≡ z
eq₁ : +→⊎ (ℕ.suc X) Y z₂ ≡ inj₁ z
z₂  : Fin (ℕ.suc X + Y)
z₁  : Fin (ℕ.suc X) ⊎ Fin Y
Y   : SomeFin
X   : ℕ

-}

invˡ' : {X Y : SomeFin} → ∀ {z₁ z₂} → z₂ ≡ ⊎→+ X Y z₁ → +→⊎ X Y z₂ ≡ z₁ 
invˡ' {ℕ.zero} {Y} {inj₂ a} {b} eq = ≡.cong inj₂ eq
invˡ' {ℕ.suc X} {Y} {inj₁ z} {b} eq with inspect = {!!}
invˡ' {ℕ.suc X} {Y} {inj₁ (s a)} {b} eq = {!!}
invˡ' {ℕ.suc X} {Y} {inj₂ a} {b} eq = {!!}


invˡ : {X Y : SomeFin} → ∀ {z₁ z₂} → z₂ ≡ ⊎→+ X Y z₁ → +→⊎ X Y z₂ ≡ z₁ 
invˡ {ℕ.zero} {Y} {inj₂ z₁} {z₂} z₂≡z₁ = ≡.cong inj₂ z₂≡z₁
invˡ {ℕ.suc X} {Y} {inj₁ z} {z} eq = ≡.refl
invˡ {ℕ.suc X} {Y} {inj₁ (s z₁)} {s z₂} eq
  with +→⊎ (ℕ.suc X) Y (s z₂) | inspect (+→⊎ (ℕ.suc X) Y) (s z₂)
     | ⊎→+ (ℕ.suc X) Y (inj₁ (s z₁)) | inspect (⊎→+ (ℕ.suc X) Y) (inj₁ (s z₁))
... | inj₁ z | [ eq₁ ] | s C | [ eq₂ ] = {!!}
... | inj₁ (s A) | [ eq₁ ] | s C | [ eq₂ ] = ≡.cong (inj₁ ∘ s) {!!}
... | inj₂ A | [ eq₁ ] | s C | [ eq₂ ] = {!!}
-- Goal z₁ ≡ z₃, This should be obvious
-- ... | inj₁ (s z₁) | [ eq₁ ] = ≡.cong (inj₁ ∘ s) {!!}
-- ... | inj₂ y | [ eq₁ ] = ⊥-elim {!!}
invˡ {ℕ.suc X} {Y} {inj₂ z₁} {z₂} eq = {!!}
--   with +→⊎ (ℕ.suc X) Y z₂ | inspect (+→⊎ (ℕ.suc X) Y) z₂
--      | ⊎→+ (ℕ.suc X) Y z₁ | inspect (⊎→+ (ℕ.suc X) Y) z₁
--      | z₁ | z₂ | +→⊎ X Y F
-- ... | inj₁ z | [ eq₁ ] | z | [ eq₂ ] | inj₁ z | z | G = ≡.refl
-- ... | inj₁ z | [ eq₁ ] | z | [ eq₂ ] | inj₁ (s E) | s F | G =
--   begin
--       +→⊎ (ℕ.suc X) Y (s F)
--     ≡⟨ {!!} ⟩
--       inj₁ (s E) ∎
-- ... | inj₁ z | [ eq₁ ] | z | [ eq₂ ] | inj₂ E | F | G =
--   begin
--       {!!}
--     ≡⟨ {!!} ⟩
--       {!!} ∎
-- ... | inj₁ (s A) | [ eq₁ ] | z | [ eq₂ ] | E | F | G = {!!}
-- ... | inj₁ A | [ eq₁ ] | s C | [ eq₂ ] | E | F | G = {!!}
-- ... | inj₂ A | [ eq₁ ] | C | [ eq₂ ] | E | F | G = {!!}


-- invˡ {ℕ.suc X} {Y} {inj₁ (s x)} {s y} eq
--   with +→⊎ X Y y | inspect (+→⊎ X Y) y | invˡ {X} {Y} {inj₁ x}
-- ... | inj₁ y' | [ eq₂ ] | _ = ≡.cong (λ i → inj₁ (s i)) {!!}
-- ... | inj₂ y' | [ eq₂ ] | D = {!!}
-- invˡ {ℕ.suc X} {Y} {inj₂ x} {y} eq = {!!}

invʳ : {X Y : SomeFin} → ∀ {x y} → y ≡ +→⊎ X Y x → ⊎→+ X Y y ≡ x
invʳ {X} {Y} w = {!!}


⊎↔+ : ∀ (X Y : SomeFin) → Fin (X + Y) ↔ (Fin X ⊎ Fin Y)
⊎↔+ X Y =
  record
    { to =  +→⊎ X Y
    ; from = ⊎→+ X Y
    ; to-cong = ≡.cong (+→⊎ X Y) 
    ; from-cong = ≡.cong (⊎→+ X Y)
    ; inverse = invˡ , invʳ
    }

{-
_-A : {x y a : ℕ} → (f : Fin (a +ℕ x) → Fin (a +ℕ y)) → {inj : injective f}
    → Σ[ f' ∈ (Fin x → Fin y) ] injective f'
_-A {a = ℕ.zero} f {inj} = f , inj
_-A {x} {y} {a = ℕ.suc a} f {inj} =
  let F = sub {x = a +ℕ x} {y = a +ℕ y} f inj
      f₂ = proj₁ F
      inj₂ = proj₂ F
  in
    proj₁ (f₂ -A) , proj₂ (f₂ -A)
-- -}
