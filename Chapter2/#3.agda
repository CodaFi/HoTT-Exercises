module #3 where

open import Relation.Binary.PropositionalEquality

{-
  Exercise 2.3 Give a fourth, different, proof of Lemma 2.1.2, and prove that it is equal to the others.
-}

based-ind₌ : ∀ {i} {A : Set i}{a : A} → (C : (x : A) → (a ≡ x) → Set i) → C a refl → {x : A} → (p : a ≡ x) → C x p
based-ind₌ C c p rewrite p = c

-- Uses based path induction 
composite''' : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite''' {i} {A} {x}{y}{_} p = based-ind₌ D d where
  D : (z : A) → (q : y ≡ z) → Set i
  D z _ = x ≡ z

  d : D _ refl
  d = p
