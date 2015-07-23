module #16 where

{-
  Show that addition of natural numbers is commutative: ∏(i,j:N)(i + j = j + i).
-}

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

l-commut₀ : (n : ℕ) → n + 0 ≡ n
l-commut₀ zero = refl
l-commut₀ (suc n) = cong suc (l-commut₀ n)

suc-in-the-middle-with-you : ∀ m n → m + suc n ≡ suc (m + n)
suc-in-the-middle-with-you zero n = refl
suc-in-the-middle-with-you (suc m) n = cong suc (suc-in-the-middle-with-you m n)

+-commutative : (m n : ℕ) → m + n ≡ n + m
+-commutative zero n = sym (l-commut₀ n)
+-commutative (suc m) n =
  begin
    (suc m) + n
      ≡⟨ refl ⟩
    suc (m + n)
      ≡⟨ cong suc (+-commutative m n) ⟩
    suc (n + m)
      ≡⟨ sym (suc-in-the-middle-with-you n m) ⟩
    n + (suc m)
  ∎
