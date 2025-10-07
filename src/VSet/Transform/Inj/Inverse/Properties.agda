module VSet.Transform.Inj.Inverse.Properties where

open import VSet.Prelude
open import Cubical.Data.Prod.Base
open import Cubical.Relation.Nullary.Properties 
open import Cubical.Data.Sum.Base hiding (elim)
open import Cubical.Data.Nat.Base hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Maybe.Base hiding (elim)
open import Cubical.Data.Maybe.Properties
open import Cubical.Data.List.Base hiding (elim; [_])
open import VSet.Data.Fin.Base
open import VSet.Data.Fin.Order
open import VSet.Data.Fin.Splice
open import VSet.Data.Fin.Properties
open import VSet.Data.Inj.Base 
open import VSet.Data.Inj.Order 
open import VSet.Transform.Inj.Elementary.Base
open import VSet.Transform.Inj.Inverse.Base
open import VSet.Transform.Inj.Inverse.Insert
open import VSet.Transform.Inj.Compose.Base

private
  variable
    l l' m m' n n' : ℕ

inv-is-apply-inv : ∀ {m} → (f : Inj m m) → (y : Fin m)
                 → apply-inv f y ≡ just (apply (inv f) y)
inv-is-apply-inv {suc m} (inc b f) y with y ≈?ᶠ b
... | yes y≈b =
  apply-inv-rec f b y (yes y≈b) ≡⟨ refl ⟩
  just fzero ≡⟨ cong just (sym (apply-insert≡b b f0 (inv f))) ⟩
  just (apply (insert b f0 (inv f)) b)
    ≡⟨ cong (λ ○ → just (apply (insert b f0 (inv f)) ○)) (≈ᶠ→≡ (≈fsym y≈b)) ⟩
  just (apply (insert b f0 (inv f)) y) ▯
... | no y≉b =
  apply-inv-rec f b y (no y≉b)
    ≡⟨ refl ⟩
  map-Maybe fsuc (apply-inv f (fjoin b y y≉b))
    ≡⟨ cong (map-Maybe fsuc) (inv-is-apply-inv f (fjoin b y y≉b)) ⟩
  map-Maybe fsuc (just (apply (inv f) (fjoin b y y≉b)))
    ≡⟨ refl ⟩
  just (fsuc (apply (inv f) (fjoin b y y≉b)))
    ≡⟨ refl ⟩
  just (apply-insert b f0 (inv f) y (no y≉b))
    ≡⟨ cong just (apply-insert-irrelevant b f0 (inv f) y (no y≉b) (y ≈?ᶠ b)) ⟩
  just (apply-insert b f0 (inv f) y (y ≈?ᶠ b))
    ≡⟨ cong just (sym (apply∘insert≡apply-insert b f0 (inv f) y)) ⟩
  just (apply (insert b f0 (inv f)) y) ▯

+suc : ∀ {m n} → m + suc n ≡ suc (m + n)
+suc {zero} {n} = refl
+suc {suc m} {n} = cong suc (+-suc m n)

insert0≡inc
  : ∀ {m} (b : Fin (suc m)) (f : Inj m m)
  → insert fzero b f ≡ inc b f
insert0≡inc b f = refl

-- Not sure if this is the easiest way to prove it. There are a lot of cases.
insert-reorder : ∀ {m n} (a1 : Fin (suc m)) (a2 : Fin (suc (suc m)))
                         (b1 : Fin (suc n)) (b2 : Fin (suc (suc n)))
               → (f : Inj m n)
               → insert a2 b2 (insert a1 b1 f)
               ≡ insert (fsplice a2 a1) (fsplice b2 b1)
                   (insert (fcross a1 a2) (fcross b1 b2) f)
insert-reorder fzero fzero b1 b2 f =
  insert f0 b2 (insert f0 b1 f)
    ≡⟨ refl ⟩
  inc b2 (inc b1 f)
    ≡⟨ {!!} ⟩
  insert f1 (fsplice b2 b1)
   (inc (fcross b1 b2) f)
    ≡⟨ refl ⟩
  insert (fsplice f0 f0) (fsplice b2 b1)
   (insert (fcross f0 f0) (fcross b1 b2) f) ▯
insert-reorder (fsuc a1) a2 b1 b2 f = {!!}
insert-reorder fzero (fsuc a2) b1 b2 f = {!!}
  -- insert a2 b2 (insert a1 b1 f)
  --   ≡⟨ {!!} ⟩
  -- insert (fsplice a2 a1) (fsplice b2 b1)
  --  (insert (fcross a1 a2) (fcross b1 b2) f) ▯

insert-comp
  : ∀ {l m n : ℕ} (b : Fin (suc m)) (f : Inj l m) (g : Inj m n)
  → insert b f0 g ∘ʲ insert f0 b f ≡ insert f0 f0 (g ∘ʲ f)
insert-comp fzero f g = refl
insert-comp (fsuc b) f (inc c g) =
  insert (fsuc b) f0 (inc c g) ∘ʲ insert f0 (fsuc b) f
    ≡⟨ refl ⟩
  insert (fsuc b) f0 (inc c g) ∘ʲ inc (fsuc b) f
    ≡⟨ {!!} ⟩
  insert f0 f0 (inc c g ∘ʲ f) ▯

insert-isInjective
  : ∀ {m} {a b : Fin (suc m)} {f g : Inj m m}
  → insert a b f ≡ insert a b g  → f ≡ g
insert-isInjective {a = fzero} {b = b} {f = f} {g = g} f'≡g' =
  proj₂ (inc-isInjective f'≡g')
insert-isInjective {a = fsuc a} {b = fzero} {f = inc c1 f} {g = inc c2 g} f''≡g'' =
  let u : insert a (fcross c1 f0) f ≡ insert a (fcross c2 f0) g
      u = (proj₂ (inc-isInjective f''≡g''))
      ins-f≡ins-g : insert a f0 f ≡ insert a f0 g
      ins-f≡ins-g = subst2 (λ ○ □ → insert a ○ f ≡ insert a □ g)
                           (fcross0≡0 c1) (fcross0≡0 c2)
                           (proj₂ (inc-isInjective f''≡g''))
      f≡g : f ≡ g
      f≡g = insert-isInjective ins-f≡ins-g
      c1≡c2 : c1 ≡ c2
      c1≡c2 = fsuc-injective $ proj₁ $ inc-isInjective f''≡g''
  in cong₂ inc c1≡c2 f≡g
insert-isInjective {a = fsuc a} {b = fsuc b} {f = inc c1 f} {g = inc c2 g} f''≡g'' =
  let c1≡c2 : c1 ≡ c2
      c1≡c2 = fsplice-isInjective (proj₁ (inc-isInjective f''≡g''))
      f≡g : f ≡ g
      f≡g = insert-isInjective (proj₂ (inc-isInjective f''≡g'')
          ∙ cong (λ ○ → insert a (fcross ○ (fsuc b)) g) (sym c1≡c2))
  in cong₂ inc c1≡c2 f≡g

f∘f⁻¹≡id : ∀ {m} (f : Inj m m) → f ∘ʲ inv f ≡ idInj m
f∘f⁻¹≡id f = {!!}

inv-inc : (f : Inj m m) → (b : Fin (suc m)) → Inj (suc m) (suc m)
inv-inc f fzero = inc fzero f
inv-inc (inc b f) (fsuc a) = inc f0 (inv-inc f a)

isInjective : ∀ {A B : Type} (f : A → B) → Type
isInjective f = ∀ x y → f x ≡ f y → x ≡ y

isSurjective : ∀ {A B : Type} (f : A → B) → Type
isSurjective {A = A} f = ∀ y → Σ[ x ∈ A ] f x ≡ y

Inj-isInjective : ∀ {m n} → (f : Inj m n) → isInjective (apply f)
Inj-isInjective (inc b f) fzero fzero fx≡fy = refl
Inj-isInjective (inc b f) fzero (fsuc y) fx≡fy =
  absurd (fsplice≉b b (apply f y) (≡→≈ᶠ (sym fx≡fy)))
Inj-isInjective (inc b f) (fsuc x) fzero fx≡fy =
  absurd (fsplice≉b b (apply f x) (≡→≈ᶠ fx≡fy))
Inj-isInjective (inc b f) (fsuc x) (fsuc y) fx≡fy =
  cong fsuc (Inj-isInjective f x y (fsplice-isInjective fx≡fy))

apply-inv≡0→b≈y : {m n : ℕ} → (f : Inj m n) → (b y : Fin (suc n))
                → apply-inv (inc b f) y ≡ just fzero
                → y ≈ᶠ b
apply-inv≡0→b≈y f b y p with y ≈?ᶠ b 
... | yes y≈b = y≈b
... | no y≉b with apply-inv f (fjoin b y y≉b)
...      | nothing = absurd (¬nothing≡just p)
...      | just x = absurd (fsuc≢fzero (just-inj (fsuc x) f0 p))
