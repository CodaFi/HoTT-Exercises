{-# OPTIONS --without-K #-}
module Formalization where

-- Sets and n-types
-- ----------------

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum

isSet : ∀ {a} → Set a → Set a
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

-- The only possible inhabitants of ⊤ is tt which means everything
-- is reflexivity.
is-1-set : isSet ⊤
is-1-set tt tt refl refl = refl

-- Ex falso quodlibet strikes again
is-0-set : isSet ⊥
is-0-set ()

is-ℕ-set : isSet ℕ
is-ℕ-set x y p q = {!!}

is-1-type : ∀ {a} → Set a → Set a
is-1-type A = (x y : A) → (p q : x ≡ y) → (r s : p ≡ q) → r ≡ s

3-1-8 : ∀ {a}{A : Set a} → isSet A → is-1-type A
3-1-8 f x y p q r s = {!!}
  where
    g : {q : x ≡ y} → (p ≡ q)
    g {q} = f x y p q

-- This defines "mere propositions"
-- If all elements of P are connected by a path, then p contains no
-- higher homotopy.
isProp : ∀ {a} → Set a → Set a
isProp P = (x y : P) → (x ≡ y)


