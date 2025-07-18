module VSet.Data.SomeFin.Properties where

open import VSet.Prelude
open import VSet.Data.Nat
open import VSet.Path
open import VSet.Data.Fin
open import VSet.Function.Injection
open import VSet.Function.Iso
open import VSet.Function.Properties

open import VSet.Data.SomeFin.Base
open import VSet.Data.SomeFin.Minus

open _∖_

module DelZeroSuc {x : ℕ} (b :  ⟦ x ⟧) where
  B : (suc x ∖ fzero)
  B = fsuc b — fzero≢fsuc b

  del-zero-suc : del fzero B ≡ b
  del-zero-suc with (del fzero B) | inspect (del fzero) B
  ... | fzero | [ p ]ᵢ = sym p
  ... | fsuc A | [ p ]ᵢ = sym p

open DelZeroSuc using (del-zero-suc)

del-suc-zero : ∀ {x} (a : ⟦ suc x ⟧)
             → del (fsuc a) (fzero — fsuc≢fzero a) ≡ fzero
del-suc-zero a = refl

del-suc-suc : ∀ {x} (a b : ⟦ suc x ⟧) → (a'≢b' : fsuc a ≢ fsuc b)
             → del (fsuc a) (fsuc b — a'≢b')
             ≡ fsuc (del a (b — ≢cong fsuc a'≢b'))
del-suc-suc {zero} fzero fzero a'≢b' = absurd (a'≢b' refl)
del-suc-suc {suc x} a b a'≢b' = refl

del-inj : {x : SomeFin} → (a : ⟦ suc x ⟧)
        → (B C : (suc x ∖ a))
        → del a B ≡ del a C
        → val B ≡ val C
del-inj {x = zero} fzero (fzero — a≢b) _ _ =
  absurd (a≢b refl)
del-inj {x = suc x} fzero (fzero — a≢b) _ _ =
  absurd (a≢b refl)
del-inj {x = suc x} fzero (fsuc _ — _) (fzero — a≢c) _ =
  absurd (a≢c refl)
del-inj {x = suc x} fzero (fsuc b — a≢b) (fsuc c — a≢c) b'≡c' =
  cong fsuc b'≡c'
del-inj {x = suc x} (fsuc a) (fzero — a≢b) (fzero — a≢c) b'≡c' =
  refl
del-inj {x = suc x} (fsuc a) (fzero — a≢b) (fsuc c — a≢c) b'≡c' =
  absurd (fzero≢fsuc (del a (c — ≢cong fsuc a≢c)) b'≡c')
del-inj {x = suc x} (fsuc a) (fsuc b — a≢b) (fzero — a≢c) b'≡c'
  = absurd (fsuc≢fzero (del a (b — ≢cong fsuc a≢b)) b'≡c')
del-inj {x = suc x} (fsuc a) (fsuc b — a≢b) (fsuc c — a≢c) b'≡c'
  = cong fsuc (del-inj {x = x} a (b — ≢cong fsuc a≢b) (c — {!!}) {!!})
--   with a | b | c
-- ... | fzero | fzero | _ = absurd (a≢b refl)
-- ... | fzero | fsuc i | fzero = absurd (a≢c refl)
-- ... | fzero | fsuc i | fsuc j =
--   let i≡j : i ≡ j
--       i≡j =
--         i
--           ≡⟨ sym (del-zero-suc i) ⟩
--         del fzero (fsuc i — a≢b)
--           ≡⟨ b'≡c' ⟩
--         del fzero (fsuc j — a≢c)
--           ≡⟨ del-zero-suc j ⟩
--         j ▯
--   in cong fsuc i≡j
-- ... | fsuc a | fzero | fzero = refl
-- ... | fsuc a | fzero | fsuc j = absurd (fzero≢fsuc {!!} b'≡c')
-- ... | fsuc a | fsuc i | fzero = absurd (fsuc≢fzero {!!} b'≡c')
-- ... | fsuc a | fsuc i | fsuc j =
--   let rec :  del a (i — _) ≡ del a (j — _) → i ≡ j
--       rec = del-inj a (i — ((λ a≡i → a≢b (cong fsuc a≡i))))
--                       (j — ((λ a≡j → a≢c (cong fsuc a≡j))))
--   in cong fsuc (rec (fsuc-injective (
--         fsuc (del a (i — _)) ≡⟨ refl ⟩
--         (del (fsuc a) ((fsuc i) — _)) ≡⟨ b'≡c' ⟩
--         (del (fsuc a) ((fsuc j) — _)) ≡⟨ refl ⟩
--         fsuc (del a (j — _ )) ▯)))


ins-inj : {x : SomeFin} → (a : ⟦ suc x ⟧)
        → (b c : Fin x)
        → val (ins a b) ≡ val (ins a c)
        → b ≡ c
ins-inj = {!!}
-- ins-inj {x = zero} a b c a+b≡a+c = absurd (Fin-absurd b)
-- ins-inj {x = suc x} a b c a+b≡a+c with a | b | c
-- ... | fzero | fzero | fzero = refl
-- ... | fzero | fzero | fsuc c' = absurd (fzero≢fsuc (fsuc-inj a+b≡a+c))
-- ... | fzero | fsuc b' | fzero = absurd (fsuc≢fzero (fsuc-inj a+b≡a+c))
-- ... | fzero | fsuc b' | fsuc c' = fsuc-inj a+b≡a+c
-- ... | fsuc a' | fzero | fzero = refl
-- ... | fsuc a' | fzero | fsuc c' = absurd (fzero≢fsuc a+b≡a+c)
-- ... | fsuc a' | fsuc b' | fzero = absurd (fsuc≢fzero a+b≡a+c)
-- ... | fsuc a' | fsuc b' | fsuc c' =
--   cong fsuc (ins-inj a' b' c' (fsuc-inj a+b≡a+c))

