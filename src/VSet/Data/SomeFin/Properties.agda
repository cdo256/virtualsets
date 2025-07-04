module VSet.Data.SomeFin.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Core.Primitives
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.SumFin.Base
open import Cubical.Data.SumFin.Properties

open import VSet.Path
-- open import VSet.Data.Fin.Default
open import VSet.Function.Base
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.SomeFin.Base

open _∖_

fzero≢fsuc : {x : SomeFin} → (a : Fin x) → fzero ≢ fsuc a
fzero≢fsuc a = {!elim!} 

fsuc≢fzero : {x : SomeFin} → (a : Fin x) → fsuc a ≢ fzero 
fsuc≢fzero a = ≢sym {!fzero≢fsuc!} 

del-zero-suc : ∀ {x} (b : ⟦ x ⟧)
             → del fzero (fsuc b , fzero≢fsuc b) ≡ b
del-zero-suc = {!!}
-- del-zero-suc b with fin-view (del fzero (fsuc b , fzero≠fsuc))
-- ... | vzero = refl
-- ... | vsuc _ = refl

del-suc-zero : ∀ {x} (a : ⟦ suc x ⟧)
             → del (fsuc a) (fzero , fsuc≢fzero a) ≡ fzero
del-suc-zero = {!!}
-- del-suc-zero a with fin-view (del (fsuc a) (fzero , fsuc≠fzero))
-- ... | vzero = refl
del-suc-suc : ∀ {x} (a b : ⟦ suc x ⟧) → .(a'≢b' : fsuc a ≢ fsuc b)
             → del (fsuc a) (fsuc b , {!!})
             ≡ fsuc (del a (b , {!λ a≡b → a'≢b' (ap fsuc a≡b)!}))
del-suc-suc = {!!}
-- del-suc-suc a b a'≢b' with fin-view (fsuc a) | fin-view (fsuc b)
-- ... | vsuc _ | vsuc _ = refl

del-inj : {x : SomeFin} → (a : ⟦ suc x ⟧)
        → (B C : (suc x ∖ a))
        → del a B ≡ del a C
        → val B ≡ val C
del-inj = {!!}
-- del-inj {x = zero} a (b , a≢b) (c , a≢c) b'≡c'
--   with fin-view b | fin-view c
-- ... | vzero | vzero = refl 
-- del-inj {x = suc x} a (b , a≢b) (c , a≢c) b'≡c'
--   with fin-view a | fin-view b | fin-view c
-- ... | vzero | vzero | _ = absurd (a≢b refl)
-- ... | vzero | vsuc i | vzero = absurd (a≢c refl)
-- ... | vzero | vsuc i | vsuc j =
--   let i≡j : i ≡ j
--       i≡j =
--         i
--           ≡˘⟨ del-zero-suc i ⟩
--         del fzero (fsuc i , a≢b)
--           ≡⟨ b'≡c' ⟩
--         del fzero (fsuc j , a≢c)
--           ≡⟨ del-zero-suc j ⟩
--         j ∎
--   in ap fsuc i≡j
-- ... | vsuc a | vzero | vzero = refl
-- ... | vsuc a | vzero | vsuc j = absurd (fzero≠fsuc b'≡c')
-- ... | vsuc a | vsuc i | vzero = absurd (fsuc≠fzero b'≡c')
-- ... | vsuc a | vsuc i | vsuc j =
--   let rec :  del a (i , _) ≡ del a (j , _) → i ≡ j
--       rec = del-inj a (i , ((λ a≡i → a≢b (ap fsuc a≡i))))
--                       (j , ((λ a≡j → a≢c (ap fsuc a≡j))))
--   in ap fsuc (rec (fsuc-inj (
--         fsuc (del a (i , _)) ≡⟨ refl ⟩
--         (del (fsuc a) ((fsuc i) , _)) ≡⟨ b'≡c' ⟩
--         (del (fsuc a) ((fsuc j) , _)) ≡⟨ refl ⟩
--         fsuc (del a (j , _ )) ∎)))


ins-inj : {x : SomeFin} → (a : ⟦ suc x ⟧)
        → (b c : Fin x)
        → val (ins a b) ≡ val (ins a c)
        → b ≡ c
ins-inj = {!!}
-- ins-inj {x = zero} a b c a+b≡a+c = absurd (Fin-absurd b)
-- ins-inj {x = suc x} a b c a+b≡a+c with fin-view a | fin-view b | fin-view c
-- ... | vzero | vzero | vzero = refl
-- ... | vzero | vzero | vsuc c' = absurd (fzero≠fsuc (fsuc-inj a+b≡a+c))
-- ... | vzero | vsuc b' | vzero = absurd (fsuc≠fzero (fsuc-inj a+b≡a+c))
-- ... | vzero | vsuc b' | vsuc c' = fsuc-inj a+b≡a+c
-- ... | vsuc a' | vzero | vzero = refl
-- ... | vsuc a' | vzero | vsuc c' = absurd (fzero≠fsuc a+b≡a+c)
-- ... | vsuc a' | vsuc b' | vzero = absurd (fsuc≠fzero a+b≡a+c)
-- ... | vsuc a' | vsuc b' | vsuc c' =
--   ap fsuc (ins-inj a' b' c' (fsuc-inj a+b≡a+c))

