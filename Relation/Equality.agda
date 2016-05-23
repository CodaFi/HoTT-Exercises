module Relation.Equality where

open import Data.Product

-- Identity Types
--

{-
  The type of identifications of two (x y : A).

  While this can be read as propositional equality, in HoTT identity
  can be (and is) elevated to a data type.
-}
data _≡_ {a}{A : Set a}(x : A) : A → Set a where
  refl : x ≡ x

cong : ∀ {a b} {A : Set a}{B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- Path Induction over the Identity Type
--
ind₌ : ∀ {a c}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set c) → ((x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → C x y p
ind₌ C c x .x refl = c x
