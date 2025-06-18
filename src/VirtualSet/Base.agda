module VirtualSet.Base where

open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Fin
  using (Fin) renaming (suc to s; zero to z)
open import Data.Fin.Properties
  using (_≟_; 0≢1+n; suc-injective)
open import Data.Nat
  using (ℕ; _+_)
open import Data.Product
  using (Σ-syntax; _×_; proj₁; proj₂)
open import Data.Product.Base as Product
  using (∃; _×_; _,_)
open import Data.Sum
  using (inj₁; inj₂)
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


open ≡-Reasoning

private
  variable
    c ℓ : Level.Level

injective : {X Y : Set} → (f : X → Y) → Set
injective {X} {Y} f = ∀ (a b : X) → f a ≡ f b → a ≡ b

module _ {x : ℕ} where

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
        → (B₁ : Σ[ b₁ ∈ Fin (ℕ.suc x) ] a ≢ b₁)
        → (B₂ : Σ[ b₂ ∈ Fin (ℕ.suc x) ] a ≢ b₂)
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
  sub : Σ[ f' ∈ (Fin x → Fin y) ] injective f'
  sub =
    let f' : Fin x → Fin y
        f' i =
          let (j , 0≢j) = add z i 
              k = f j
              l = del (f z) (k , λ f0≡fj → 0≢j (inj z j f0≡fj))
          in l
    in f' , (λ a b f'a≡f'b →
      let (a₁ , 0≢a₁) = add z a
          (b₁ , 0≢b₁) = add z b 
          a₂ = f a₁
          b₂ = f b₁
          a₃ = del (f z) (a₂ , (λ f0≡fa₁ → 0≢a₁ (inj z a₁ f0≡fa₁)))
          b₃ = del (f z) (b₂ , (λ f0≡fb₁ → 0≢b₁ (inj z b₁ f0≡fb₁)))
          X = inj a₁ b₁ {!!}
      in {!!})

--with (i ≟ z)
--... | yes i≡0 = {!!}
--... | no i≢0 = {!!}

_-A : {x y a : ℕ} → (f : Fin (a + x) → Fin (a + y)) → {inj : injective f}
    → Σ[ f' ∈ (Fin x → Fin y) ] injective f'
_-A {a = ℕ.zero} f {inj} = f , inj
_-A {a = ℕ.suc a} f = {!!}

