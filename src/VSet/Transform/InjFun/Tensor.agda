module VSet.Transform.InjFun.Tensor where

open import VSet.Prelude
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import Cubical.Data.Nat.Properties

open import VSet.Data.Nat using (ℕ; zero; suc; _+_)
open import VSet.Data.Fin renaming (pred to fpred)
open import VSet.Data.Sum.Properties
open import VSet.Data.InjFun.Injection
open import VSet.Data.InjFun.Equality
open import VSet.Data.Fin.SumSplit
open import VSet.Transform.InjFun.Pred
open import VSet.Transform.InjFun.Compose
open import VSet.Data.InjFun.Properties

tensor : ∀ {k l m n : ℕ} → [ k ↣ l ] → [ m ↣ n ] → [ k + m ↣ l + n ]
tensor {k} {l} {m} {n} f g = ≅to↣ (⊎≅+ l n) ↣∘↣ ↣-map-⊎ f g ↣∘↣ ≅to↣ (flip-≅ (⊎≅+ k m))

𝟘 : [ 0 ↣ 0 ]
𝟘 = ↣-id ⟦ 0 ⟧

infixl 30 _⊕_

_⊕_ : ∀ {k l m n : ℕ} → [ k ↣ l ] → [ m ↣ n ] → [ k + m ↣ l + n ]
f ⊕ g = tensor f g

id⊕id≡id : {m n : ℕ} → ⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n ≡ id
id⊕id≡id {m} {n} =
  ⊎→+ m n ∘ ⊎-map id id ∘ +→⊎ m n
    ≡⟨ cong (λ ○ → ⊎→+ m n ∘ ○ ∘ +→⊎ m n) ⊎-map-id≡id ⟩
  ⊎→+ m n ∘ +→⊎ m n
    ≡⟨ funExt (sect m n) ⟩
  id ▯

Id⊕Id≈Id : {m n : ℕ} → Id {m} ⊕ Id {n} ≈ Id {m + n}
Id⊕Id≈Id {m} {n} = record { p = refl ; q = refl ; path = id⊕id≡id }

Id⊕Id≡Id : {m n : ℕ} → Id {m} ⊕ Id {n} ≡ Id {m + n}
Id⊕Id≡Id {m} {n} = cong₂ _,_ id⊕id≡id s
  where r : subst is-injective id⊕id≡id (snd (Id {m} ⊕ Id {n})) ≡ snd (Id {m + n})
        r = isProp-is-injective id (subst is-injective id⊕id≡id (snd (Id {m} ⊕ Id {n}))) (snd (Id {m + n}))
        s : (λ i → is-injective (id⊕id≡id i))
          [ snd (Id {m} ⊕ Id {n}) ≡ snd (Id {m + n}) ]
        s = compPathP' (subst-filler is-injective id⊕id≡id (snd (Id {m} ⊕ Id {n}))) r

ladd : ∀ {l m : ℕ} → (A : ℕ) → [ l ↣ m ] → [ A + l ↣ A + m ]
ladd {l} {m} A f = (↣-id ⟦ A ⟧) ⊕ f

radd : ∀ {l m : ℕ} → (A : ℕ) → [ l ↣ m ] → [ l + A ↣ m + A ]
radd {l} {m} A f = f ⊕ (↣-id ⟦ A ⟧)

⊕-preserves-∘
  : ∀ {m m' m'' n n' n''}
  → (f : [ m ↣ m' ]) (f' : [ m' ↣ m'' ]) (g : [ n ↣ n' ]) (g' : [ n' ↣ n'' ])
  → (f' ∘ʲ f) ⊕ (g' ∘ʲ g) ≈ (f' ⊕ g') ∘ʲ (f ⊕ g)
⊕-preserves-∘ {m} {m'} {m''} {n} {n'} {n''} f f' g g' =
  record { p = refl ; q = refl ; path = e }
  where
    e : ⊎→+ m'' n'' ∘ ⊎-map (fst f' ∘ fst f) (fst g' ∘ fst g) ∘ +→⊎ m n
      ≡ (⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ +→⊎ m' n')
      ∘  (⊎→+ m' n' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n)
    e =
      ⊎→+ m'' n'' ∘ ⊎-map (fst f' ∘ fst f) (fst g' ∘ fst g) ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m'' n'' ∘ ○ ∘ +→⊎ m n)
                (sym (⊎-map-∘ (fst f) (fst f') (fst g) (fst g'))) ⟩
      ⊎→+ m'' n'' ∘ (⊎-map (fst f') (fst g') ∘ ⊎-map (fst f) (fst g)) ∘ +→⊎ m n
        ≡⟨ cong (λ ○ → ⊎→+ m'' n'' ∘ (⊎-map (fst f') (fst g') ∘ ○ ∘ ⊎-map (fst f) (fst g)) ∘ +→⊎ m n)
                (sym (funExt (retr m' n'))) ⟩
      ⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ (+→⊎ m' n' ∘
        ⊎→+ m' n') ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n
        ≡⟨ refl ⟩
      (⊎→+ m'' n'' ∘ ⊎-map (fst f') (fst g') ∘ +→⊎ m' n') ∘
        ⊎→+ m' n' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ m n ▯

module _ {l l' m m' n n' : ℕ} where
  α-p-dom : l + (m + n) ≡ (l + m) + n
  α-p-dom = +-assoc l m n

  α-p-cod : l' + (m' + n') ≡ (l' + m') + n'
  α-p-cod = +-assoc l' m' n'

  α-p : [ (l + (m + n)) ↣ (l' + (m' + n')) ]
      ≡ [ ((l + m) + n) ↣ ((l' + m') + n') ]
  α-p = cong₂ [_↣_] (+-assoc l m n) (+-assoc l' m' n')

  α-p-fun : (Fin (l + (m + n)) → Fin (l' + (m' + n')))
          ≡ (Fin ((l + m) + n) → Fin ((l' + m') + n'))
  α-p-fun = cong₂ FinFun (+-assoc l m n) (+-assoc l' m' n')

  α-iso : Iso [ (l + (m + n)) ↣ (l' + (m' + n')) ]
              [ ((l + m) + n) ↣ ((l' + m') + n') ]
  α-iso = pathToIso α-p

  α : [ (l + (m + n)) ↣ (l' + (m' + n')) ]
    → [ ((l + m) + n) ↣ ((l' + m') + n') ]
  α = Iso.fun α-iso

  α⁻¹ : [ ((l + m) + n) ↣ ((l' + m') + n') ]
      → [ (l + (m + n)) ↣ (l' + (m' + n')) ]
  α⁻¹ = Iso.inv α-iso

funPath→InjFunPath : {m m' : ℕ} → (f g : [ m ↣ m' ])
                   → fst f ≡ fst g → f ≡ g
funPath→InjFunPath {m} {m'} (f , f-inj) (g , g-inj) f≡g =
  f , f-inj
    ≡⟨ cong₂ _,_ f≡g (subst-filler is-injective f≡g f-inj) ⟩
  g , f-inj'
    ≡⟨ cong (g ,_)
            (isProp-is-injective
              g f-inj' g-inj) ⟩
  g , g-inj ▯
  where
    f-inj' : is-injective g
    f-inj' = subst is-injective f≡g f-inj

mapsplit-l
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → ⊎-map (⊎→+ l' m' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ l m) (fst h)
  ≡   ⊎-map (⊎→+ l' m') id
    ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
    ∘ ⊎-map (+→⊎ l m) id
mapsplit-l {l} {l'} {m} {m'} {n} {n'} f g h =
  ⊎-map (⊎→+ l' m' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ l m) (id ∘ fst h ∘ id)
    ≡⟨ sym (⊎-map-∘ _ _ _ _) ⟩
    ⊎-map (⊎→+ l' m') id
  ∘ ⊎-map (⊎-map (fst f) (fst g) ∘ +→⊎ l m) (fst h)
    ≡⟨ sym (cong (⊎-map (⊎→+ l' m') id ∘_) (⊎-map-∘ _ _ _ _)) ⟩
    ⊎-map (⊎→+ l' m') id
  ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
  ∘ ⊎-map (+→⊎ l m) id ▯

mapsplit-r
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → ⊎-map (fst f) (⊎→+ m' n' ∘ ⊎-map (fst g) (fst h) ∘ +→⊎ m n)
  ≡   ⊎-map id (⊎→+ m' n')
    ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
    ∘ ⊎-map id (+→⊎ m n)
mapsplit-r {l} {l'} {m} {m'} {n} {n'} f g h =
  ⊎-map (id ∘ fst f ∘ id) (⊎→+ m' n' ∘ ⊎-map (fst g) (fst h) ∘ +→⊎ m n)
    ≡⟨ sym (⊎-map-∘ _ _ _ _) ⟩
    ⊎-map id (⊎→+ m' n')
  ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h) ∘ +→⊎ m n)
    ≡⟨ sym (cong (⊎-map id (⊎→+ m' n') ∘_) (⊎-map-∘ _ _ _ _)) ⟩
    ⊎-map id (⊎→+ m' n')
  ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
  ∘ ⊎-map id (+→⊎ m n) ▯

expand-l
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → fst ((f ⊕ g) ⊕ h) ≡
      ⊎→+ (l' +ℕ m') n'
    ∘ ⊎-map (⊎→+ l' m') id
    ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
    ∘ ⊎-map (+→⊎ l m) id
    ∘ +→⊎ (l +ℕ m) n
expand-l {l} {l'} {m} {m'} {n} {n'} f g h =
  fst ((f ⊕ g) ⊕ h)
    ≡⟨ refl ⟩
  ⊎→+ (l' +ℕ m') n' ∘ ⊎-map (fst (f ⊕ g)) (fst h) ∘ +→⊎ (l +ℕ m) n
    ≡⟨ refl ⟩
    ⊎→+ (l' +ℕ m') n'
  ∘ ⊎-map (⊎→+ l' m' ∘ ⊎-map (fst f) (fst g) ∘ +→⊎ l m) (fst h)
  ∘ +→⊎ (l +ℕ m) n
    ≡⟨ (cong (λ ○ → _ ∘ ○ ∘ _) (mapsplit-l f g h)) ⟩
    ⊎→+ (l' +ℕ m') n'
  ∘ ⊎-map (⊎→+ l' m') id
  ∘ ⊎-map (⊎-map (fst f) (fst g)) (fst h)
  ∘ ⊎-map (+→⊎ l m) id
  ∘ +→⊎ (l +ℕ m) n ▯

expand-r
  : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → fst (f ⊕ (g ⊕ h)) ≡
      ⊎→+ l' (m' +ℕ n')
    ∘ ⊎-map id (⊎→+ m' n')
    ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
    ∘ ⊎-map id (+→⊎ m n)
    ∘ +→⊎ l (m +ℕ n)
expand-r {l} {l'} {m} {m'} {n} {n'} f g h =
  fst (f ⊕ (g ⊕ h))
    ≡⟨ refl ⟩
  ⊎→+ l' (m' +ℕ n') ∘ ⊎-map (fst f) (fst (g ⊕ h)) ∘ +→⊎ l (m +ℕ n)
    ≡⟨ refl ⟩
  ⊎→+ l' (m' +ℕ n')
  ∘ ⊎-map (fst f)
           (⊎→+ m' n' ∘ ⊎-map (fst g) (fst h) ∘ +→⊎ m n)
  ∘ +→⊎ l (m +ℕ n)
    ≡⟨ (cong (λ ○ → _ ∘ ○ ∘ _) (mapsplit-r f g h)) ⟩
  ⊎→+ l' (m' +ℕ n')
  ∘ ⊎-map id (⊎→+ m' n')
  ∘ ⊎-map (fst f) (⊎-map (fst g) (fst h))
  ∘ ⊎-map id (+→⊎ m n)
  ∘ +→⊎ l (m +ℕ n) ▯


assoc : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → ((f ⊕ g) ⊕ h) ≡ α {l} {l'} (f ⊕ (g ⊕ h))
assoc {l} {l'} {m} {m'} {n} {n'} f g h =
  funPath→InjFunPath ((f ⊕ g) ⊕ h) (α (f ⊕ (g ⊕ h))) {!fun-assoc!}

unassoc : {l l' m m' n n' : ℕ}
  → (f : [ l ↣ l' ]) (g : [ m ↣ m' ]) (h : [ n ↣ n' ])
  → (f ⊕ (g ⊕ h)) ≡ (α⁻¹ {l} {l'}) ((f ⊕ g) ⊕ h)
unassoc {l} {l'} {m} {m'} {n} {n'} f g h =
  let α-p = α-p {l} {l'} {m} {m'} {n} {n'}
  in
  (f ⊕ (g ⊕ h))
    ≡⟨ sym (transport⁻Transport α-p (f ⊕ (g ⊕ h))) ⟩
  transport (sym α-p )
    (transport α-p (f ⊕ (g ⊕ h)))
    ≡⟨ sym (cong (transport (sym α-p)) (assoc f g h)) ⟩
  transport (sym α-p) ((f ⊕ g) ⊕ h) ▯


-- α₁ : ∀ {m m' m'' n n' n''}
--    → (f : [ m ↣ n ]) (g : [ m' ↣ n' ]) (h : [ m'' ↣ n'' ])
--    → f ⊕ (g ⊕ h) → {!(f ⊕ g) ⊕ h!}

-- ⊕-triangle : ∀ {m m' n n'} → (f : [ m ↣ n ]) (g : [ m' ↣ n' ])
--            → {!!}
