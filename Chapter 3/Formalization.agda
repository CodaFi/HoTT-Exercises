module Formalization where

-- Sets and n-types
-- ----------------

open import Relation.Binary.PropositionalEquality

isSet : ∀ {a} → Set a → Set a
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

is-1-type : ∀ {a} → Set a → Set a
is-1-type A = (x y : A) → (p q : x ≡ y) → (r s : p ≡ q) → r ≡ s

3-1-8 : ∀ {a}{A : Set a} → isSet A → is-1-type A
3-1-8 f x y p q r s = {!!}
  where
    g : {q : x ≡ y} → (p ≡ q)
    g {q} = f x y p q

