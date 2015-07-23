module #13 where

{-
  Using propositions-as-types, derive the double negation of the principle of excluded
  middle, i.e. prove not (not (P or not P)).
-}

open import Data.Sum
open import Relation.Nullary

excluded-middle : (P : Set) → ¬ (¬ (P ⊎ (¬ P)))
excluded-middle P z = z (inj₂ (λ x → z (inj₁ x)))
