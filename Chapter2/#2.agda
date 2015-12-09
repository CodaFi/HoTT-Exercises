module #2 where

open import Relation.Binary.PropositionalEquality
open import #1

{-
Exercise 2.2. Show that the three equalities of proofs constructed in the previous exercise form a 
commutative triangle. In other words, if the three definitions of concatenation are denoted by 
(p ∘ q), (p ∘ q), and (p ∘ q), then the concatenated equality

         (p ∘ q) = (p ∘ q) = (p ∘ q)

is equal to the equality (p ∘ q) = (p ∘ q).
-}

composite-commutative-triangle : ∀ {i} {A : Set i}{x y z : A} → (p : x ≡ y) (q : y ≡ z) →
    composite (composite=composite' p q) (composite'=composite'' p q) ≡ composite=composite'' p q
composite-commutative-triangle refl refl = refl
