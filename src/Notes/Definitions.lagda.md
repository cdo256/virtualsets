```
module Notes.Definitions where
open import VSet.Prelude
open import Cubical.Data.Nat
```

I am using the inductive definition of Fin, as in the standard library. Note that this is distinct from the 1Lab and Agda Cubical definitions so I had to recreate it. (Justify why this was necessary).

```
data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)
```

I make use of some simple utility functions. `pred` is the predecessor
of an element, `fshift` increases every element in `Fin y` by a fixed
amount, expanding the domain to `Fin (x + y)`. `finject` is a related
funciton to fshift; it takes Fin x to Fin (x + y) by simply expanding
the domain, keeping the values fixed. `finj` takes Fin x to Fin (suc x),
which is sometimes easier to work with. than `finject`.

```
pred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
pred fzero = fzero
pred (fsuc n) = n

fshift : (x : ℕ) → {y : ℕ} → Fin y → Fin (x + y)
fshift zero a = a
fshift (suc x) a = fsuc (fshift x a)

finject : {x : ℕ} → (y : ℕ) → Fin x → Fin (x + y)
finject {suc _} _ fzero = fzero
finject {suc x} y (fsuc a) = fsuc (finject {x} y a)

finj : {x : ℕ} → (a : Fin x) → Fin (suc x)
finj fzero = fzero
finj (fsuc a) = fsuc (finj a)
```



Each injective funtion funciton works by constructing the graph of the funciton injectively. This is a bit less intuitive than simply using `Fin m → Fin n`, but has some nice features:
 - There is exactly 1 Inj for every inductive Fin funciton.
 - All Inj graphs are injective by construction.
 - This could be (relatively) easy to extended to coinductive types.

See also `Notes/InjExplained`.

```
data Inj : ℕ → ℕ → Type where
  nul : ∀ n → Inj 0 n
  inc : ∀ {m n} → (b : Fin (suc n))
      → (inj : Inj m n)
      → Inj (suc m) (suc n)
```

Note that `fsplice` is one of a family of operations on Fin that provide utilities for iswapping indexed (?) types.

`fsplice b` maps `Fin x` to `Fin (suc x)` in such a way that b is not
in the codomain. Essentially it increments all values above (or equal to b and
keeps the values less than b unchanged. 

```
fsplice : ∀ {x} → (b : Fin (suc x)) → (a : Fin x) → Fin (suc x)
fsplice fzero a = fsuc a
fsplice (fsuc b) fzero = fzero
fsplice (fsuc b) (fsuc a) = fsuc (fsplice b a)
```

`fcross` is in some ways the opposite to `fsplice`.
The idea is that given a pivot point `b`, it creates a funciton that
'merges' the adjacent codomain elements located at `b` and `b + 1`.

```
fcross : ∀ {x : ℕ} → (b : Fin x) → (a : Fin (suc x)) → Fin x
fcross fzero fzero = fzero
fcross (fsuc b) fzero = fzero
fcross fzero (fsuc a) = a
fcross (fsuc b) (fsuc a) = fsuc (fcross b a)
```

```agda-uneval
open import VSet.Data.Fin.Order

fjoin-cases : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
                → Trichotomyᶠ a b → Fin x
fjoin-cases b a a≉b (flt a<b) = fin-restrict-< a a<b
fjoin-cases b a a≉b (feq a≈b) = absurd (a≉b a≈b)
fjoin-cases b (fsuc a) a≉b (fgt b<a) = a

fjoin : ∀ {x : ℕ} → (b a : Fin (suc x)) → a ≉ᶠ b
           → Fin x
fjoin b a a≉b = fjoin-cases b a a≉b (a ≟ᶠ b)
```

`fjoin` is like `fcross` but it ensures that the pivot `b` is not in
the domain, by taking `a ≉ᶠ b`. This ensure that fjoin and fsplice are
exact inverses.

These work with an apply function given below.

```
apply : ∀ {m n} → Inj m n → Fin m → Fin n
apply (inc b inj) fzero = b
apply (inc b inj) (fsuc a) =
  fsplice b (apply inj a)
```

We can the define identity like so,

```
Id : ∀ {m} → Inj m m
Id {zero} = nul zero
Id {suc m} = inc fzero (Id {m})
```

We then define some elementary operations that we will build on to
make to build up properties about virtual sets:

```
-- Insert a pair, and shift domain and codomain over.
insert : ∀ {m n} → (a : Fin (suc m)) → (b : Fin (suc n))
       → (f : Inj m n) → Inj (suc m) (suc n)
insert fzero b f = inc b f
insert (fsuc a) b (inc c f) =
  inc (fsplice b c) (insert a (fcross c b) f)

-- Take out one element and shift everything back one place.
remove : ∀ {m n} → (a : Fin (suc m))
       → (f : Inj (suc m) (suc n)) → Inj m n
remove fzero (inc b f) = f
remove {suc m} {suc n} (fsuc a) (inc c f) =
  inc (fcross (apply f a) c) (remove a f) 

-- Splice all outputs around a pivot b 
bubble : ∀ {m n} → (b : Fin (suc n))
       → (f : Inj m n) → Inj m (suc n)
bubble b (nul _) = nul _
bubble b (inc c f) =
  inc (fsplice b c) (bubble (fcross c b) f)

-- Remove from the domain without shifting the codomain.
excise : ∀ {m n} → (a : Fin (suc m))
       → (f : Inj (suc m) (suc n)) → Inj m (suc n)
excise a f = bubble (apply f a) (remove a f)
```

From here we can define compose inductively, by seeing where each link
ends up under composition. `b ≡ apply (inc b f) f0`, so `apply (g ∘ʲ
inc b f)
f0 ≡ apply g b`, therefore the first link should be from f0 to `apply
g b`. We then remove the link from the composition and recurse.

```
_∘ʲ_ : ∀ {l m n} (g : Inj m n) (f : Inj l m) → Inj l n 
_∘ʲ_ g (nul _) = nul _
_∘ʲ_ {suc l} {suc m} {suc n} g (inc b f) =
  inc (apply g b) (remove b g ∘ʲ f)
```

A parital inverse is given by `apply-inv`. It recursively checks if
any of the links ends in the target element `b`, returning either the
match or nothing if there are no matches. Since Inv is known to
injective, there can only be 1 or 0 matches for each codomain element.

```agda-uneval
apply-inv-rec : {m n : ℕ} → (f : Inj m n) → (b y : Fin (suc n)) → Dec (y ≈ᶠ b) → Maybe (Fin (suc m))
apply-inv : {m n : ℕ} → (f : Inj m n) → (y : Fin n) → Maybe (Fin m)

apply-inv-rec f b y (yes y≈b) = just fzero
apply-inv-rec f b y (no y≉b) =
  map-Maybe fsuc (apply-inv f (fjoin b y y≉b))

apply-inv (nul _) _ = nothing
apply-inv (inc b f) y = apply-inv-rec f b y (y ≈?ᶠ b)
```

`inv` is a full inverse, which is exactly when m ≡ n. It simply works recurively inserting each link to the recursive call.

```
inv : ∀ {m} → (f : Inj m m) → Inj m m
inv {zero} (nul zero) = nul zero
inv {suc m} (inc c f) = insert c fzero (inv f)
```

The tensor operation is implemnted, by making use of `finject` and
`shift`. `shift` takes a function f and increases every codomain
elemnet by a fixed amount.

```
shift1 : ∀ {m n} → (f : Inj m n) → Inj m (suc n)
shift1 (nul _) = nul _
shift1 (inc b f) = inc (fsuc b) (shift1 f)

shift : ∀ {m n} → (l : ℕ) → (f : Inj m n) → Inj m (l + n)
shift zero f = f
shift (suc l) f = shift1 (shift l f)
```

This lets us define tensor `f ⊕ g` which works by recursing on f,
adding the link with finject. Once it reaches the end of the links
from `f`,

It starts by shifting g and then recursively adds links from f.

TODO diagram.

```
_⊕_ : ∀ {m m' n n'} → (f : Inj m m') → (g : Inj n n') → Inj (m + n) (m' + n')
nul m' ⊕ g = shift m' g
inc b f ⊕ g = inc (finject _ b) (f ⊕ g)

𝟘 : Inj 0 0
𝟘 = nul 0
```

There is an alternate representation to `shift` which recurses on the
structure of f first rather than the offset. It has to make use of
subst since `l + suc n` is not definitionally equal to `suc (l + n)`.

```
shift' : ∀ {m n} → (l : ℕ) → (f : Inj m n) → Inj m (l + n)
shift' {m = 0} l (nul _) = nul (l + _)
shift' {m = suc m} {n = suc n} l (inc b f) =
  subst2 Inj refl (sym p) $ inc (subst Fin p (fshift l b)) (shift' l f)
  where p = +-suc l n
```
