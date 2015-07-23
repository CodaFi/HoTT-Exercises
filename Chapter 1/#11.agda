module #11 where

{-
  Show that for any type A, we have ¬¬¬A → ¬A.
-}

open import Data.Empty
open import Relation.Nullary

tripleNeg : ∀{x}{A : Set x} → ¬ (¬ (¬ A)) → ¬ A 
tripleNeg = λ z z₁ → z (λ z₂ → z₂ z₁)
