module #9 where

{-
  Define the type family Fin : N → U mentioned at the end of §1.3, and the dependent
  function fmax : ∏(n:N) Fin(n + 1) mentioned in §1.4.
-}

open import Data.Nat

data Fin : ℕ → Set where
  FZ : {n : ℕ} → Fin (suc n)
  FS : {n : ℕ} → Fin n → Fin (suc n)

fmax : (n : ℕ) → Fin (n + 1)
fmax zero = FZ
fmax (suc n) = FS (fmax n)
