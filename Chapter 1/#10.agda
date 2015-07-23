module #10 where

{-
  Exercise 1.10. Show that the Ackermann function ack : N → N → N is definable using only
  recN satisfying the following equations:
-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality

recₙ : ∀{c}{C : Set c} → C → (ℕ → C → C) → ℕ → C
recₙ c₀ cₛ zero = c₀
recₙ c₀ cₛ (suc n) = cₛ n (recₙ c₀ cₛ n)

ack : ℕ → ℕ → ℕ
ack zero n = suc n
ack (suc m) zero = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)

ack-rec : ℕ → ℕ → ℕ
ack-rec = recₙ suc (λ m cont → recₙ (cont 1) (λ _ n → cont n))

{- The process of proving this might destroy my computer, so no.
ack-β : (n m : ℕ) → ack m n ≡ ack-rec m n
ack-β m n = {!!}
-}
