module #2 where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

{-
Exercise 1.2. Derive the recursion principle for products recA×B using only the projections, and
verify that the definitional equalities are valid. Do the same for Σ-types.
-}

module Products { a b c }{A : Set a}{B : Set b}{C : Set c}(g : A → B → C) where

  recₓ :  A × B → C
  recₓ x = g (proj₁ x) (proj₂ x) 

  rec-β : (x : A)(y : B) → recₓ (x , y) ≡ g x y
  rec-β x y = refl

module Sums { a b c }{A : Set a}{B : A → Set b}{C : Set c}(g : (x : A) → B x → C) where
  
  rec-Σ : Σ A B → C
  rec-Σ x = g (proj₁ x) (proj₂ x)

  rec-Σ-β : (x : A)(y : B x) → rec-Σ (x , y) ≡ g x y
  rec-Σ-β x y = refl
