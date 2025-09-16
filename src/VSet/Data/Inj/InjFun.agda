module VSet.Data.Inj.InjFun where

open import VSet.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Nat.Order
open import VSet.Function.Iso
open import VSet.Function.Injection
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base
open import VSet.Data.Inj.Properties
open import VSet.Data.InjFun.Injection
open import VSet.Data.InjFun.Equality

Inj→InjFun : {m n : ℕ} → Inj m n → [ m ↣ n ]
Inj→InjFun f = apply f , apply-Inj-isInjective f

-- InjFun→m≤n : {m n : ℕ} → [ m ↣ n ] → m ≤ n
-- InjFun→m≤n {zero} {n} f = zero-≤ 
-- InjFun→m≤n {suc m} {zero} (f , _) = Fin0-absurd (f f0)
-- InjFun→m≤n {suc m} {suc n} f = suc-≤-suc (InjFun→m≤n {!!})

InjFun-fx'≉f0 : {m n : ℕ} (f : [ suc m ↣ suc n ]) → (x : ⟦ m ⟧)
              → (fst f) (fsuc x) ≉ᶠ (fst f) f0
InjFun-fx'≉f0 (f , f-inj) x fx'≈f0 =
  fsuc≢fzero (f-inj (fsuc x) f0 (≈ᶠ→≡ fx'≈f0))

reduce-f : {m n : ℕ} → [ suc m ↣ suc n ] → ⟦ m ⟧ → ⟦ n ⟧
reduce-f (f , f-inj) a =
  fjoin (f f0) (f (fsuc a)) (InjFun-fx'≉f0 (f , f-inj) a)

reduce-inj : {m n : ℕ} → (f : [ suc m ↣ suc n ]) → is-injective (reduce-f f)
reduce-inj (f , f-inj) x y gx≡gy =
  fsuc-injective (f-inj (fsuc x) (fsuc y) fx'≡fy')
  where
    fx'≡fy' : f (fsuc x) ≡ f (fsuc y)
    fx'≡fy' = fjoin-isInjective
      (f f0) (f (fsuc x)) (f (fsuc y))
      (InjFun-fx'≉f0 (f , f-inj) x)
      (InjFun-fx'≉f0 (f , f-inj) y)
      gx≡gy

reduce : {m n : ℕ} → [ suc m ↣ suc n ] → [ m ↣ n ]
reduce f = reduce-f f , reduce-inj f

InjFun→Inj : {m n : ℕ} → [ m ↣ n ] → Inj m n
InjFun→Inj {zero} {n} (f , f-inj) = nul _
InjFun→Inj {suc m} {zero} (f , f-inj) = Fin0-absurd (f f0)
InjFun→Inj {suc m} {suc n} (f , f-inj) =
  inc (f fzero) (InjFun→Inj (reduce (f , f-inj)))

InjFun→Inj-irrelevant : {m n : ℕ} → (f g : [ m ↣ n ]) → fst f ≡ fst g
                      → InjFun→Inj f ≡ InjFun→Inj g
InjFun→Inj-irrelevant {zero} {n} (f , f-inj) (g , g-inj) f≡g = refl
InjFun→Inj-irrelevant {suc m} {zero} (f , f-inj) (g , g-inj) f≡g = Fin0-absurd (f f0)
InjFun→Inj-irrelevant {suc m} {suc n} (f , f-inj) (g , g-inj) p =
  InjFun→Inj (f , f-inj)
    ≡⟨ refl ⟩
  inc (f fzero) (InjFun→Inj (reduce-f (f , f-inj) , reduce-inj (f , f-inj)))
    ≡⟨ refl ⟩
  inc (f f0) (InjFun→Inj ((λ a → fjoin (f f0) (f (fsuc a)) (InjFun-fx'≉f0 (f , f-inj) a))
                            , reduce-inj (f , f-inj)))
    ≡⟨ (λ i → inc (f f0)
        (InjFun→Inj-irrelevant ((λ a → fjoin (f f0) (f (fsuc a)) (InjFun-fx'≉f0 (f , f-inj) a)) , reduce-inj (f , f-inj))
                               ((λ a → fjoin (f f0) (f (fsuc a)) (InjFun-fx'≉f0 (f , f-inj') a)) , reduce-inj (f , f-inj'))
                               (funExt r ) i)) ⟩
  inc (f f0) (InjFun→Inj ((λ a → fjoin (f f0) (f (fsuc a))
                                       (λ fa'≈f0 → fsuc≢fzero (f-inj' (fsuc a) f0 (≈ᶠ→≡ fa'≈f0))))
                            , reduce-inj (f , f-inj')))
    ≡⟨ refl ⟩
  inc (f f0) (InjFun→Inj (reduce-f (f , f-inj') , reduce-inj (f , f-inj')))
    ≡⟨ refl ⟩
  InjFun→Inj (f , f-inj')
    ≡⟨ (λ i → InjFun→Inj (p i , subst-filler is-injective (sym p) g-inj (~ i))) ⟩
  InjFun→Inj (g , g-inj) ▯
  where
    f-inj' : is-injective f
    f-inj' = subst is-injective (sym p) g-inj
    r : (a : Fin m)
      → fjoin (f f0) (f (fsuc a)) (InjFun-fx'≉f0 (f , f-inj) a)
      ≡ fjoin (f f0) (f (fsuc a)) (InjFun-fx'≉f0 (f , f-inj') a)
    r a = fjoin-irrelevant (f f0) (f (fsuc a)) (InjFun-fx'≉f0 (f , f-inj) a) (InjFun-fx'≉f0 (f , f-inj') a)


sect : ∀ {m n} → (f : Inj m n) → InjFun→Inj {m} {n} (Inj→InjFun f) ≡ f
sect {zero} {n} (nul n) = refl
sect {suc zero} {suc n} (inc b (nul n)) =
  InjFun→Inj (Inj→InjFun (inc b (nul n)))
    ≡⟨ refl ⟩
  InjFun→Inj (apply (inc b (nul n)) , apply-Inj-isInjective (inc b (nul n)))
    ≡⟨ refl ⟩
  inc b (nul n) ▯
sect {suc (suc m)} {suc (suc n)} (inc b f) =
  InjFun→Inj (Inj→InjFun (inc b f))
    ≡⟨ refl ⟩
  InjFun→Inj (apply (inc b f) , apply-Inj-isInjective (inc b f))
    ≡⟨ {!refl!} ⟩
  inc (apply (inc b f) fzero) (InjFun→Inj (reduce (apply (inc b f) , apply-Inj-isInjective (inc b f))))
    ≡⟨ {!!} ⟩
  -- inc (reduce-f (g , gInj) f0)
  --     (InjFun→Inj (reduce (reduce-f (g , gInj), reduce-inj (g , gInj))))
  --   ≡⟨ cong₂ inc reduce-f0≡b sectIH ⟩
  inc b f ▯
  where
    g      = apply (inc b f)
    gInj   = apply-Inj-isInjective (inc b f)
    sectIH = sect f
    reduce-f0≡b = fjoin-fsplice-inverse b (apply f f0)
                   λ x → fsuc≢fzero (gInj (fsuc f0) f0 (≈ᶠ→≡ x))


-- sect : ∀ {m n} → (f : Inj m n) → InjFun→Inj {m} {n} (Inj→InjFun f) ≡ f
-- sect {zero} {n} (nul n) = refl
-- sect {suc zero} {suc n} (inc b (nul n)) =
--   InjFun→Inj (Inj→InjFun (inc b (nul n)))
--     ≡⟨ refl ⟩
--   InjFun→Inj (apply (inc b (nul n)) , apply-Inj-isInjective (inc b (nul n)))
--     ≡⟨ refl ⟩
--   inc b (nul n) ▯
-- sect {suc (suc m)} {suc (suc n)} (inc b f) =
--   InjFun→Inj (Inj→InjFun (inc b f))
--     ≡⟨ refl ⟩
--   InjFun→Inj (apply (inc b f) , apply-Inj-isInjective (inc b f))
--     ≡⟨ refl ⟩
--   inc b (InjFun→Inj (reduce (g , g-inj)))
--     ≡⟨ cong (inc b) r ⟩
--   inc b f ▯
--   where
--     g = apply (inc b f)
--     g-inj = apply-Inj-isInjective (inc b f)
--     h : ⟦ suc m ⟧ → ⟦ suc n ⟧
--     h a = fjoin (g f0) (g (fsuc a)) (InjFun-fx'≉f0 (g , g-inj) a)
--     h-inj : is-injective h
--     h-inj x y hx≡hy = fsuc-injective $ g-inj (fsuc x) (fsuc y) $
--       fjoin-isInjective (g f0) (g (fsuc x)) (g (fsuc y))
--                         (InjFun-fx'≉f0 (g , g-inj) x) (InjFun-fx'≉f0 (g , g-inj) y)
--                         hx≡hy
--     s : fst (reduce (g , g-inj)) ≡ fst (Inj→InjFun f)
--     s = fst (reduce (g , g-inj))
--           ≡⟨ refl ⟩
--         reduce-f (g , g-inj)
--           ≡⟨ refl ⟩
--         (λ a → fjoin (apply (inc b f) f0) (apply (inc b f) (fsuc a)) (InjFun-fx'≉f0 (g , g-inj) a))
--           ≡⟨ refl ⟩
--         (λ a → fjoin b (fsplice b (apply f a)) (λ ga'≈g0 → fsuc≢fzero (g-inj (fsuc a) f0 (≈ᶠ→≡ ga'≈g0))))
--           ≡⟨ funExt (λ a → fjoin-fsplice-inverse b (apply f a) λ ga'≈g0 → fsuc≢fzero (g-inj (fsuc a) f0 (≈ᶠ→≡ ga'≈g0))) ⟩
--         (λ a → apply f a)
--           ≡⟨ refl ⟩
--         fst (Inj→InjFun f) ▯
--     r : InjFun→Inj (reduce (g , g-inj)) ≡ f
--     r =
--       InjFun→Inj (reduce (g , g-inj))
--         ≡⟨ refl ⟩
--       InjFun→Inj (reduce-f (g , g-inj) , reduce-inj (g , g-inj))
--         ≡⟨ refl ⟩
--       inc (reduce-f (g , g-inj) f0)
--           (InjFun→Inj (reduce (reduce-f (g , g-inj) , reduce-inj (g , g-inj))))
--         ≡⟨ cong₂ inc refl {!r!} ⟩
--       inc (fjoin (g f0) (g f1) (InjFun-fx'≉f0 (g , g-inj) f0))
--           {!!}
--         ≡⟨ {!!} ⟩
--       f ▯

retr : ∀ {m n} → retract (InjFun→Inj {m} {n}) Inj→InjFun
retr f = {!!}

InjFun≅Inj : ∀ {m n} → Iso [ m ↣ n ] (Inj m n)
InjFun≅Inj = iso InjFun→Inj Inj→InjFun {!!} {!!}
