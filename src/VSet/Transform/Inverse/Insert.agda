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

apply-insert-irrelevant
  : ∀ {m} → (a : Fin (suc m)) → (b : Fin (suc m)) → (f : Inj m m)
  → (x : Fin (suc m)) → (u v : Dec (x ≈ᶠ a))
  → apply-insert a b f x u ≡ apply-insert a b f x v
apply-insert-irrelevant a b f x (yes u) (yes v) = refl
apply-insert-irrelevant a b f x (yes u) (no v) = absurd (v u)
apply-insert-irrelevant a b f x (no u) (yes v) = absurd (u v)
apply-insert-irrelevant a b f x (no u) (no v) =
  cong (fsplice b ∘ apply f) (funsplice-irrelevant a x u v)

fsplice-fsplice-fsplice-antisplice
  : ∀ {m} → (b : Fin (suc (suc m))) → (x : Fin m) → (c : Fin (suc m)) 
  → fsplice (fsplice b c) (fsplice (antisplice c b) x)
  ≡ fsplice b (fsplice c x)
fsplice-fsplice-fsplice-antisplice fzero fzero fzero = refl
fsplice-fsplice-fsplice-antisplice fzero fzero (fsuc c) = refl
fsplice-fsplice-fsplice-antisplice fzero (fsuc x) fzero = refl
fsplice-fsplice-fsplice-antisplice fzero (fsuc x) (fsuc c) = refl
fsplice-fsplice-fsplice-antisplice (fsuc b) fzero fzero = refl
fsplice-fsplice-fsplice-antisplice (fsuc b) fzero (fsuc c) = refl
fsplice-fsplice-fsplice-antisplice (fsuc b) (fsuc x) fzero = refl
fsplice-fsplice-fsplice-antisplice (fsuc b) (fsuc x) (fsuc c) =
  cong fsuc (fsplice-fsplice-fsplice-antisplice b x c)

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
    ≡⟨ cong (fsplice (fsplice b c))
            (apply-insert-irrelevant
              a (antisplice c b) f x
              (x ≈?ᶠ a) (no (≉pred x'≉a'))) ⟩
  fsplice (fsplice b c) (apply-insert a (antisplice c b) f x
                                      (no (≉pred x'≉a'))) 
    ≡⟨ refl ⟩
  fsplice (fsplice b c) (fsplice (antisplice c b) (apply f (funsplice a x (≉pred x'≉a'))))
    ≡⟨ fsplice-fsplice-fsplice-antisplice b (apply f (funsplice a x (≉pred x'≉a'))) c ⟩
  fsplice b (fsplice c (apply f (funsplice a x (≉pred x'≉a'))))
    ≡⟨ refl ⟩
  fsplice b (apply (inc c f) (fsuc (funsplice a x (≉pred x'≉a')))) 
    ≡⟨ cong (fsplice b ∘ apply (inc c f)) (sym (fsuc-funsplice a x (≉pred x'≉a'))) ⟩
  fsplice b (apply (inc c f) (funsplice (fsuc a) (fsuc x) (≉fsuc (≉pred x'≉a')))) 
    ≡⟨ cong (fsplice b ∘ apply (inc c f))
            (funsplice-irrelevant (fsuc a) (fsuc x)
              (≉fsuc (≉pred x'≉a')) x'≉a') ⟩
  fsplice b (apply (inc c f) (funsplice (fsuc a) (fsuc x) x'≉a')) 
    ≡⟨ refl ⟩
  apply-insert (fsuc a) b (inc c f) (fsuc x) (no x'≉a') ▯
