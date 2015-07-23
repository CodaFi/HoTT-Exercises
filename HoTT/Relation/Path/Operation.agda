{-# OPTIONS --without-K #-}
module Relation.Path.Operation where

open import Relation.Equality

infixr 4 _∘_
infix 9 _⁻¹

-- Path inversion
_⁻¹ : ∀ {a}{A : Set a}{x y : A} → (x ≡ y) → (y ≡ x)
_⁻¹ = ind₌ (λ x y _ → y ≡ x) (λ _ → refl) _ _

-- Composition of paths
_∘_ : {A : Set}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∘_ {z = z} = ind₌ (λ x y _ → y ≡ z → x ≡ z) (λ _ p → p) _ _

