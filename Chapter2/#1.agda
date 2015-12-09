{-# OPTIONS --without-K #-}

module #1 where

open import Relation.Binary.PropositionalEquality

{-
Exercise 2.1. Show that the three obvious proofs of Lemma 2.1.2 are pairwise equal.
-}

ind₌ : ∀{a b}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set b) → ((x : A) → C x x refl) → {x y : A} → (p : x ≡ y) → C x y p
ind₌ C c {x}{y} p rewrite p = c y

composite : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite {i} {A} {_}{_}{z} p = ind₌ D d p where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y _ = y ≡ z → x ≡ z

  d : (x₁ : A) → D x₁ x₁ refl
  d _ = λ x → x

composite' : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite' {i} {A} {_}{_}{z} = ind₌ D d where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y _ = y ≡ z → x ≡ z

  d : (x : A) → D x x refl
  d x = ind₌ E e where
    E : (x z : A) → (q : x ≡ z) → Set i
    E x z _ = x ≡ z

    e : (x : A) → E x x refl
    e x = refl

composite'' : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite'' refl refl = refl

composite=composite' : ∀ {i} {A : Set i}{x y z : A} → (p : x ≡ y)(q : y ≡ z) → composite p q ≡ composite' p q
composite=composite' refl refl = refl

composite=composite'' : ∀ {i} {A : Set i}{x y z : A} → (p : x ≡ y)(q : y ≡ z) → composite p q ≡ composite'' p q
composite=composite'' refl refl = refl

composite'=composite'' : ∀ {i} {A : Set i}{x y z : A} → (p : x ≡ y)(q : y ≡ z) → composite' p q ≡ composite'' p q
composite'=composite'' refl refl = refl



