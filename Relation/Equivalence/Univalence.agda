module Relation.Equivalence.Univalence where

open import Basics
open import Level
open import Relation.Equality
open import Data.Product

-- For any A and B, a quasi-inverse of f is a triple with
--    ∘ A way back (an inverse for the homomorphism)
--    ∘ Homotopies:
--        ⊚ α : f ∘ g ∼ id
--        ⊚ β : g ∘ f ∼ id
-- For now, because I am lazy, the presence of a quasi-inverse will count
-- as our definition of equivalence for now.  Sorry.
record IsEquiv {i j}{A : Set i}{B : Set j}(to : A → B) : Set (i ⊔ j) where
  field
    from : B → A
    iso₁ : (x : A) → from (to x) ≡ x
    iso₂ : (y : B) → to (from y) ≡ y

-- Example 2.4.7: Identity is an equivalence.
id-is-equiv : ∀ {i} (A : Set i) → IsEquiv (id {i}{A})
id-is-equiv {i} A = record
  { from = id {i}{A}
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl
  }

-- Type equivalence is also an equivalence, just on the Universe because:
--    ∘ id-is-equiv works for it, therefore A ≃ A
--    ∘ With A ≃ B, we can always make B ≃ A
--    ∘ With A ≃ B and B ≃ C we have A ≃ C 
_≃_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
A ≃ B = Σ (A → B) IsEquiv

postulate -- Just kidding
  ua : ∀ {i} {{A : Set i}}{{B : Set i}} → (A ≃ B) ≃ (A ≡ B)
-- ^This says "equivalent types may be identified"

