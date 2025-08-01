module VSet.Transform.Inverse.Insert where

open import VSet.Prelude
open import Cubical.Data.Nat.Base hiding (elim)
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice 
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inverse.Base
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Relation.Nullary.Base 

private
  variable
    l l' m m' n n' : ℕ

apply-insert≡b
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → (apply (insert a b f) a)
  ≡ b
apply-insert≡b fzero fzero (nul 0) = refl
apply-insert≡b fzero b f =
  apply (insert fzero b f) fzero ≡⟨ refl ⟩
  apply (inc b f) fzero ≡⟨ refl ⟩
  b ▯
apply-insert≡b (fsuc a) b (inc c f) =
  apply (insert (fsuc a) b (inc c f)) (fsuc a)
    ≡⟨ refl ⟩
  apply (inc (fsplice b c) (insert a (antisplice c b) f)) (fsuc a)
    ≡⟨ refl ⟩
  fsplice (fsplice b c) (apply (insert a (antisplice c b) f) a)
    ≡⟨ cong (fsplice (fsplice b c))
            (apply-insert≡b a (antisplice c b) f) ⟩
  fsplice (fsplice b c) (antisplice c b)
    ≡⟨ splice-splice-antisplice b c ⟩
  b ▯

apply-insert 
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → (x : Fin (suc m)) → Dec (x ≈ᶠ a)
  → Fin (suc m)
apply-insert a b f x (yes x≈a) = b
apply-insert a b f x (no x≉a) = fsplice b (apply f (funsplice a x x≉a)) 

≉pred : ∀ {x y} {a : Fin x} {b : Fin y} → fsuc a ≉ᶠ fsuc b → a ≉ᶠ b
≉pred a'≉b' a≈b = a'≉b' (≈fsuc a≈b)

fsplice-lemma1 
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc (suc m))) → (f : Inj m m)
  → (x : Fin (suc m)) → (c : Fin (suc m)) → (x'≉a' : fsuc x ≉ᶠ fsuc a)
  → fsplice (fsplice b c) (apply-insert a (antisplice c b) f x
                                        (x ≈?ᶠ a)) 
  ≡ fsplice b (apply (inc c f) (fsuc (funsplice a x (≉pred x'≉a')))) 
fsplice-lemma1 a b f x c x'≉a' with x ≟ᶠ a
... | flt x<a =
  fsplice (fsplice b c)
   (apply-insert a (antisplice c b) f x (no (<ᶠ→≉ x<a)))
   ≡⟨ {!!} ⟩
  fsplice b
   (fsplice c
    (apply f
     (funsplice-cases a x (λ a≈b → x'≉a' (≈fsuc a≈b)) (flt x<a)))) ▯
... | feq x≈a = absurd (x'≉a' (≈fsuc x≈a))
... | fgt x>a = 
  fsplice (fsplice b c)
   (apply-insert a (antisplice c b) f x (no (≉fsym (<ᶠ→≉ x>a))))
   ≡⟨ {!!} ⟩
  fsplice b
   (fsplice c
    (apply f
     (funsplice-cases a x (λ a≈b → x'≉a' (≈fsuc a≈b)) (fgt x>a)))) ▯


apply∘insert≡apply-insert
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → (x : Fin (suc m))
  → (apply (insert a b f) x)
  ≡ apply-insert a b f x (x ≈?ᶠ a)
apply∘insert≡apply-insert a b f x with x ≈?ᶠ a
apply∘insert≡apply-insert a b f x | yes x≈a =
  cong (apply (insert a b f)) (≈ᶠ→≡ x≈a) ∙ apply-insert≡b a b f
apply∘insert≡apply-insert fzero b f fzero | no x≉a = absurd (x≉a ≈fzero)
apply∘insert≡apply-insert fzero b f (fsuc x) | no x≉a =
  apply (insert fzero b f) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc b f) (fsuc x)
    ≡⟨ refl ⟩
  fsplice b (apply f x)
    ≡⟨ refl ⟩
  fsplice b (apply f (funsplice fzero (fsuc x) x≉a))
    ≡⟨ refl ⟩
  apply-insert fzero b f (fsuc x) (no x≉a) ▯
apply∘insert≡apply-insert (fsuc a) b (inc c f) fzero | no x≉a =
  apply (insert (fsuc a) b (inc c f)) f0
    ≡⟨ refl ⟩
  fsplice b c
    ≡⟨ refl ⟩
  fsplice b (apply (inc c f) f0)
    ≡⟨ refl ⟩
  fsplice b (apply (inc c f) (funsplice (fsuc a) fzero x≉a))
    ≡⟨ refl ⟩
  apply-insert (fsuc a) b (inc c f) f0 (no x≉a) ▯
apply∘insert≡apply-insert (fsuc a) b (inc c f) (fsuc x) | no x'≉a' =
  apply (insert (fsuc a) b (inc c f)) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc (fsplice b c) (insert a (antisplice c b) f)) (fsuc x)
    ≡⟨ refl ⟩
  fsplice (fsplice b c) (apply (insert a (antisplice c b) f) x) 
    ≡⟨ cong (fsplice (fsplice b c))
            (apply∘insert≡apply-insert
              a (antisplice c b) f x) ⟩
  fsplice (fsplice b c) (apply-insert a (antisplice c b) f x
                                      (x ≈?ᶠ a)) 
    ≡⟨ {!!} ⟩
  fsplice b (apply (inc c f) (fsuc (funsplice a x (≉pred x'≉a')))) 
    ≡⟨ cong (fsplice b ∘ apply (inc c f)) (sym (fsuc-funsplice a x (≉pred x'≉a'))) ⟩
  fsplice b (apply (inc c f) (funsplice (fsuc a) (fsuc x) (≉fsuc (≉pred x'≉a')))) 
    ≡⟨ cong (fsplice b ∘ apply (inc c f))
            (funsplice-irrelevant (fsuc a) (fsuc x)
              (≉fsuc (≉pred x'≉a')) x'≉a') ⟩
  fsplice b (apply (inc c f) (funsplice (fsuc a) (fsuc x) x'≉a')) 
    ≡⟨ refl ⟩
  apply-insert (fsuc a) b (inc c f) (fsuc x) (no x'≉a') ▯

apply-insert-≢-0
  : ∀ {m} → (a : Fin (suc m)) → (f : Inj m m)
  → (x : Fin (suc m)) → (a≢x : a ≢ x)
  → apply (insert a f0 f) x
  ≡ {!fsplice ? {!apply f ?!}!}
apply-insert-≢-0 fzero f fzero 0≢0 = absurd (0≢0 refl)
apply-insert-≢-0 fzero f (fsuc x) _ =
  apply (insert f0 f0 f) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc f0 f) (fsuc x)
    ≡⟨ refl ⟩
  {!fsplice f0 (apply f x)!} ▯
apply-insert-≢-0 (fsuc a) (inc c f) fzero a'≢0 =
  apply (insert (fsuc a) f0 (inc c f)) f0 
    ≡⟨ refl ⟩
  apply (inc (fsplice f0 c) (insert a (antisplice c f0) f)) f0 
    ≡⟨ refl ⟩
  fsplice f0 c
    ≡⟨ {!!} ⟩
  fsplice {!!} {!!} ▯
apply-insert-≢-0 (fsuc a) (inc c f) (fsuc x) a'≢x' with a ≟ᶠ x
... | flt a<x =
  apply (insert (fsuc a) f0 (inc c f)) (fsuc x)
    ≡⟨ refl ⟩
  apply (inc (fsplice f0 c) (insert a (antisplice c f0) f)) (fsuc x)
    ≡⟨ refl ⟩
  fsplice (fsplice f0 c) (apply (insert a (antisplice c f0) f) x)
    ≡⟨ {!!} ⟩
  fsplice (fsuc c) (apply (insert a (antisplice c f0) f) x)
    ≡⟨ {!!} ⟩
  {!!} ▯
... | feq a≈x = absurd (≢cong fsuc a'≢x' (≈ᶠ→≡ a≈x))
... | fgt a>x = {!!}
