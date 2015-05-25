module OnePointTwelve where

{-
  Using the propositions as types interpretation, derive the following tautologies.
  (i) If A, then (if B then A).
  (ii) If A, then not (not A).
  (iii) If (not A or not B), then not (A and B).
-}

open import Data.Product
open import Data.Sum
open import Relation.Nullary

const : {A B : Set} → A → (B → A)
const = λ z _ → z

double-negation : {A : Set} → A → ¬ (¬ A)
double-negation = λ z z₁ → z₁ z

demorgans-law₁ : {A B C : Set} → ((¬ A) ⊎ (¬ B)) → (¬ (A × B))
demorgans-law₁ (inj₁ ¬x) (a , _) =  ¬x a
demorgans-law₁ (inj₂ ¬y) (_ , b) =  ¬y b
