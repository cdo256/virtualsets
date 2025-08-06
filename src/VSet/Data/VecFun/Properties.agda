module VSet.Data.VecFun.Properties where

open import VSet.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec hiding (lookup)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.VecFun.Base
open import VSet.Data.Inj.Base
open import VSet.Transform.Elementary.Base

Inj→VecFun : {m n : ℕ} → Inj m n → VecFun m n
Inj→VecFun (nul _) = []
Inj→VecFun (inc b f) = b ∷ Inj→VecFun (bubble b f)

splice→cross
  : ∀ {n : ℕ} → (b : Fin (suc n)) (c : Fin n) (d : Fin n)
  → fsplice (fsplice b c) d ≡ b
  → d ≡ fcross c b
splice→cross fzero fzero fzero eq' = refl
splice→cross fzero fzero (fsuc d) eq' = absurd (fsuc≢fzero (fsuc d) eq')
splice→cross fzero (fsuc c) fzero eq' = refl
splice→cross fzero (fsuc c) (fsuc d) eq' = absurd (fsuc≢fzero (fsplice (fsuc c) d) eq')
splice→cross (fsuc b) fzero d eq' = fsuc-injective eq'
splice→cross (fsuc b) (fsuc c) fzero eq' = absurd (fzero≢fsuc b eq')
splice→cross (fsuc b) (fsuc c) (fsuc d) eq' = cong fsuc (splice→cross b c d (fsuc-injective eq'))

b∉bubble : ∀ {m n : ℕ} → (b : Fin (suc n)) → (f : Inj m n) → b ∉ʲ bubble b f
b∉bubble b (inc c f) (fzero , f'a≡b) = fsplice≉b b c (≡→≈ᶠ f'a≡b)
b∉bubble b (inc c f) (fsuc a , f'a≡b) =
  let
    u : apply (bubble (fcross c b) f) a ≡ fcross c b
    u = splice→cross b c (apply (bubble (fcross c b) f) a) f'a≡b
  in absurd (b∉bubble (fcross c b) f (a , u))

-- lookup-reduce
--   : {m n : ℕ} → (f : Inj m n) → (a : Fin m) (b : Fin (suc n))(c : Fin (suc (suc n))) 
--   → lookup (Inj→VecFun (bubble (fsplice c b) (bubble (fcross b c) f))) a ≡ c
--   → lookup (Inj→VecFun (bubble (fcross b c) f)) a ≡ fcross b c
-- lookup-reduce f fzero fzero fzero x = {!!}
-- lookup-reduce f (fsuc a) fzero fzero x = {!!}
-- lookup-reduce f a (fsuc b) fzero x = {!!}
-- lookup-reduce f a b (fsuc c) x = {!!}

swap-bubble
  : {m n : ℕ} → (f : Inj m n) → (b : Fin (suc (suc n))) (c : Fin (suc n))
  → bubble b (bubble c f) ≡ bubble (fsplice b c) (bubble (fcross c b) f)
swap-bubble (nul _) b c = refl
swap-bubble (inc d f) b c = cong₂ inc u v
  where
    u : fsplice b (fsplice c d)
      ≡ fsplice (fsplice b c) (fsplice (fcross c b) d)
    u = sym (fsplice-fsplice-fsplice-fcross b d c)
    w : bubble (fcross (fsplice c d) b)
               (bubble (fcross d c) f)
      ≡ bubble (fsplice (fcross (fsplice c d) b) (fcross d c))
               (bubble (fcross (fcross d c) (fcross (fsplice c d) b)) f)
    w = swap-bubble f (fcross (fsplice c d) b) (fcross d c)
    x : fsplice (fcross (fsplice c d) b) (fcross d c)
      ≡ (fcross (fsplice (fcross c b) d) (fsplice b c))
    x = fsplice-fcross-fcross-fsplice b c d
    y : fcross (fcross d c) (fcross (fsplice c d) b)
      ≡ fcross d (fcross c b)
    y = fcross-fcross-fcross-fsplice b c d
    v : bubble (fcross (fsplice c d) b)
               (bubble (fcross d c) f)
      ≡ bubble (fcross (fsplice (fcross c b) d) (fsplice b c))
               (bubble (fcross d (fcross c b)) f)
    v = w ∙ cong₂ (λ ○ □ → bubble ○ (bubble □ f)) x y

lookup-Inj→VecFun-bubble≢c
  : {m n : ℕ} → (f : Inj m n) → (a : Fin m) (c : Fin (suc n))
  → lookup (Inj→VecFun (bubble c f)) a ≢ c
lookup-Inj→VecFun-bubble≢c (inc b f) fzero c =
  ≉ᶠ→≢ (fsplice≉b c b)
lookup-Inj→VecFun-bubble≢c (inc b f) (fsuc a) c eq' =
  let
    u : c ∉ʲ bubble c (bubble b f)
    u = b∉bubble c (bubble b f) 
    y : bubble (fsplice c b) (bubble (fcross b c) f) ≡ bubble c (bubble b f)
    y = sym (swap-bubble f c b)
    v : c ∉ʲ bubble (fsplice c b) (bubble (fcross b c) f)
    v = subst (c ∉ʲ_) (sym y) u
    x : lookup (Inj→VecFun (bubble (fsplice c b) (bubble (fcross b c) f))) a
      ≢ c
    x eq2 = v (a , {!eq'!})
  in {!!}

lookup-bubble≡apply
  : {m n : ℕ} → (f : Inj m n) → (a : Fin m) → (b : Fin (suc n))
  → lookup (Inj→VecFun (bubble b f)) a ≡ fsplice b (apply f a)
lookup-bubble≡apply (inc c f) fzero b = refl
lookup-bubble≡apply (inc c f) (fsuc a) b =
  lookup (Inj→VecFun (bubble b (inc c f))) (fsuc a)
    ≡⟨ refl ⟩
  lookup (Inj→VecFun (inc (fsplice b c) (bubble (fcross c b) f))) (fsuc a)
    ≡⟨ refl ⟩
  lookup (fsplice b c ∷
          Inj→VecFun (bubble (fsplice b c) (bubble (fcross c b) f)))
         (fsuc a)
    ≡⟨ refl ⟩
  lookup (Inj→VecFun (bubble (fsplice b c) (bubble (fcross c b) f))) a
    ≡⟨ lookup-bubble≡apply (bubble (fcross c b) f) a (fsplice b c) ⟩
  fsplice (fsplice b c) (apply (bubble (fcross c b) f) a)
    ≡⟨ {!!} ⟩
  fsplice b (fsplice c (apply f a))
    ≡⟨ refl ⟩
  fsplice b (apply (inc c f) (fsuc a)) ▯

lookupVecFun≡applyInj
  : {m n : ℕ} → (f : Inj m n) → (a : Fin m)
  → lookup (Inj→VecFun f) a ≡ apply f a
lookupVecFun≡applyInj (inc b f) fzero = refl
lookupVecFun≡applyInj (inc b f) (fsuc a) =
  lookup (Inj→VecFun (inc b f)) (fsuc a)
    ≡⟨ refl ⟩
  lookup (Inj→VecFun (bubble b f)) a
    ≡⟨ {!!} ⟩
  fsplice b (apply f a)
    ≡⟨ refl ⟩
  apply (inc b f) (fsuc a) ▯

Inj→VecFun-isInjective
  : {m n : ℕ} → (f : Inj m n) → isInjective (Inj→VecFun f)
Inj→VecFun-isInjective f fzero fzero fa≡fb = refl
Inj→VecFun-isInjective (inc c f) fzero (fsuc b) fa≡fb =
  absurd (lookup-Inj→VecFun-bubble≢c f b c (sym fa≡fb)) 
Inj→VecFun-isInjective (inc c f) (fsuc a) fzero fa≡fb =
  absurd (lookup-Inj→VecFun-bubble≢c f a c fa≡fb) 
Inj→VecFun-isInjective (inc c f) (fsuc a) (fsuc b) fa≡fb =
  cong fsuc (Inj→VecFun-isInjective (bubble c f) a b fa≡fb)

Inj→VecInj : {m n : ℕ} → Inj m n → VecInj m n
Inj→VecInj f = Inj→VecFun f , Inj→VecFun-isInjective f
