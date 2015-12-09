module #4 where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Nat

{-
  Exercise 2.4. Define, by induction on n, a general notion of n-dimensional path in a 
  type A, simultaneously with the type of boundaries for such paths.
-}

-- We need pointed sets for this part
Set• : ∀ i → Set _
Set• i = Σ (Set i) λ X → X

Ω₁ : ∀ {i} → Set• i → Set• i
Ω₁ (X , x) = ((x ≡ x) , refl)

Ωⁿ : ∀ {i} → ℕ → Set• i → Set• _
Ωⁿ 0 x = x
Ωⁿ (suc n) x = Ωⁿ n (Ω₁ x)
