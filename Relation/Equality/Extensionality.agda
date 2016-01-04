module Relation.Equality.Extensionality where

open import Relation.Equality
open import Data.Inductive.Higher.Interval
open import Relation.Path.Operation

funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
funext {A = A}{B = B} {f = f}{g = g} p = ap {f = h} path-seg
  where
    h : I → (x : A) → B x
    h i x = interval-rec (f x) (g x) (p x) i
