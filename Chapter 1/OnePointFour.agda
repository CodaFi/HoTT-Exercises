module OnePointFour where

open import Data.Nat
open import Data.Product

iter : ∀{k}{C : Set k} → C → (C → C) → ℕ → C
iter c0 cs zero = c0
iter c0 cs (suc n) = cs (iter c0 cs n)

ind-ℕ : ∀{k}{C : ℕ → Set k} → C zero → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
ind-ℕ c0 cs zero = c0
ind-ℕ c0 cs (suc n) = cs n (ind-ℕ c0 cs n)

rec : ∀{k}{C : Set k} → C → (ℕ → C → C) → ℕ → C
rec {i}{C} c0 f n = proj₂ (iter z (λ p → (suc (proj₁ p) , f (proj₁ p) (proj₂ p))) n)
  where
    z : ℕ × C
    z = (0 , c0)
