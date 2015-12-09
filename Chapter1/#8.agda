module #8 where

{-
  Define multiplication and exponentiation using recN. Verify that (N, +, 0, ×, 1) is
  a semiring using only indN. You will probably also need to use symmetry and transitivity of
  equality, Lemmas 2.1.1 and 2.1.2.
-}

open import Data.Nat

recₙ : ∀{c}{C : Set c} → C → (ℕ → C → C) → ℕ → C
recₙ c₀ cₛ zero = c₀
recₙ c₀ cₛ (suc n) = cₛ n (recₙ c₀ cₛ n)

mul-recₙ : ℕ → ℕ → ℕ
mul-recₙ n = recₙ 0 (λ _ z → z + n)

exp-recₙ : ℕ → ℕ → ℕ
exp-recₙ n = recₙ 1 (λ _ z → z * n)

ind-ℕ : ∀{k}{C : ℕ → Set k} → C zero → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
ind-ℕ c0 cs zero = c0
ind-ℕ c0 cs (suc n) = cs n (ind-ℕ c0 cs n)

record Semiring (X : Set) : Set where
  field
    ε : X
    _⊕_ : X → X → X
    _⊛_ : X → X → X
open Semiring {{...}} public

natIsSemiring : Semiring ℕ
natIsSemiring = record { ε = zero
                       ; _⊕_ = _+_
                       ; _⊛_ = _*_
                       }

{- Semiring Laws Follow -}


