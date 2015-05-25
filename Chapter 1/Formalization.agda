module Formalization where

module Introduction where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Iso (A B : Set): Set where
  iso : (f : A → B) → (g : B → A) → (((x : A) → (g (f x)) ≡ x) × ((y : B) → (f (g y)) ≡ y))  → Iso A B

open import Function using (_∘_)

-- NB: This says every [total] relation can be refined to a function.
-- Kind of ew...
-- The Hott Book notes that though the system is strong enough to sufficiently
-- dilute the consequences of AC, the law of the excluded middle is inconsistent with Univalence
-- because it acts like a "Hilbertian Choice Operator" [p 9].
axiom-of-choice : {A : Set}
       → {B : A → Set}
       → {R : (a : A) → B a → Set}
       → (∀ (x : A) → Σ[ y ∈ B x ](R x y)) -- If for every x : A, ∃ a y : B x s.t. R x y
       → Σ[ f ∈ ((x : A) → B x)](∀ (x : A) → (R x (f x))) -- then ∃ f : A → B s.t. ∀ x : A we have R (x, f(x))
axiom-of-choice g = proj₁ ∘ g , proj₂ ∘ g 
