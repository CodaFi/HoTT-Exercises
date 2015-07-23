module #7 where

{-
Exercise 1.7. Give an alternative derivation of ind′=A from ind=A which avoids the use of universes. 
(This is easiest using concepts from later chapters.)
-}

open import Relation.Binary.PropositionalEquality

ind'₌A : ∀{a}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set) → ((x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → C x y p
ind'₌A = {!!}
