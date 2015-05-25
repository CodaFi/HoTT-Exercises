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

module Chapter where

-- Simple Polymorphic Functions
-- ----------------------------

id : ∀{a}{A : Set a} → A → A
id x = x

swap : ∀{a b c}{A : Set a}{B : Set b}{C : Set c} → (A → B → C) → (B → A → C)
swap g = λ b a → g a b

-- Product Types
-- -------------

-- To specify a type (a la Martin Lof's TT) we need:
-- ∘ Formation Rules ("We can form f : A → B when A : Type and B : Type")
-- ∘ Introduction Rules (Constructors)
-- ∘ Elimination Rules (How to use the type's elements)
-- ∘ Computation Rules (How Elimination Rules act on constructors)
-- OPTIONAL
-- ∘ Uniqueness Principle (Every element of the type is {uniquely} determined by the result of applying Elimination Rules)

-- Formation and Introduction of Pairs is given in Data.Product, so here's an Eliminator

{- Need function extensionality here, but I'm too lazy to postulate it right now.
elimₓ-β : {A B C : Set} → (f : (A × B) → C) → (g : (A → B → C)) → (x : A)(y : B) → (f (x , y) ≡ g x y)
elimₓ-β = λ f g x y → refl
-}

-- The projection functons also count as eliminators, but are too specific on occaision
-- so we introduce the recursor for product types.

recₓ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c} → (A → B → C) → (A × B) → C
recₓ g (a , b) = g a b

-- Then define the projection functions in terms of it.

pr₁ : ∀{a b}{A : Set a}{B : Set b} → (A × B) → A
pr₁ = recₓ λ a → λ b → a

pr₂ : ∀{a b}{A : Set a}{B : Set b} → (A × B) → B
pr₂ = recₓ λ a → λ b → b

-- The Unit Type also has a recursor:

open import Data.Unit

rec₁ : ∀{c}{C : Set c} → C → ⊤ → C
rec₁ c ⋆ = c

-- For dependent functions over the product type, we must first generalize the recursor

recₓ-general : ∀{a b c}{A : Set a}{B : Set b}{C : (A × B) → Set c} → (x : A × B) → (g : (a : A) → (b : B) → C (a , b)) → C x
recₓ-general = λ x g → g (pr₁ x) (pr₂ x)

-- Now we can prove the propositional uniqueness principle

uppt : ∀{a b}{A : Set a}{B : Set b} → (x : A × B) → ((pr₁ x) , (pr₂ x) ≡ x)
uppt x = refl

-- And compute the following equality:

reflₓ : ∀{a b}{A : Set a}{B : Set b}
      → (x : A)(y : B) -- ∀ x, y
      → ((pr₁ (x , y)) , (pr₂ (x , y)) ≡ (x , y)) -- Forming from forming then eliminating is the same as forming
reflₓ x y = refl

-- Now the induction function for product types;

indₓ :  ∀{a b c}{A : Set a}{B : Set b}{C : (A × B) → Set c}
     → ((x : A) → (y : B) -- ∀ x , y
     → C (x , y)) -- and a property that holds for the product (x , y)
     → (x : A × B) → C x -- ∀ products x, C holds
indₓ g (a , b) =  g a b

-- And for the unit type

ind₁ : ∀{c}{C : ⊤ → Set c} → C tt → (x : ⊤) → C x
ind₁ c ⋆ = c

-- "Induction enables us to prove the propositional uniqueness principle for 1, which asserts that its
-- only inhabitant is ⋆. That is, we can construct"

upun : {x : ⊤} → x ≡ tt
upun = refl

-- The uniqueness of unit can also be asserted by induction

upun-ind : {x : ⊤} → x ≡ tt
upun-ind = {!!}
