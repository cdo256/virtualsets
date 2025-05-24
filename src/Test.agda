open import Categories.Category
open import Data.Nat
  using (ℕ; _≤_)
open import Level
  using (0ℓ; Level; zero; suc)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning


id≤ : {n : ℕ} → n ≤ n
id≤ {ℕ.zero} = _≤_.z≤n
id≤ {ℕ.suc n} = _≤_.s≤s (id≤ {n}) 

_∘≤_ : {l m n : ℕ} → m ≤ n → l ≤ m → l ≤ n
_∘≤_ {ℕ.zero} {m} {n} m≤n 0≤m = _≤_.z≤n
_∘≤_ {ℕ.suc l} {ℕ.suc m} {ℕ.suc n} (_≤_.s≤s m≤n) (_≤_.s≤s l≤m) =
  _≤_.s≤s (m≤n ∘≤ l≤m)

Nat≤ : Category 0ℓ 0ℓ 0ℓ
Nat≤ = record
  { Obj = ℕ
  ; _⇒_ = _≤_
  ; _≈_ = _≡_
  ; id = id≤
  ; _∘_ = _∘≤_
  ; assoc = _
  ; sym-assoc = _
  ; identityˡ = _
  ; identityʳ = _
  ; identity² = _
  ; equiv = _
  ; ∘-resp-≈ = _
  }
