module #8 where

open import Data.Nat

ind-ℕ : ∀{k}{C : ℕ → Set k} → C zero → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
ind-ℕ c0 cs zero = c0
ind-ℕ c0 cs (suc n) = cs n (ind-ℕ c0 cs n)

