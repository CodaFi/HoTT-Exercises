{-# OPTIONS --without-K #-}
module Relation.Path.Operation where

open import Basics
open import Relation.Equality
open import Data.Product

infixr 4 _∙_
infix 9 _⁻¹

-- Path inversion
_⁻¹ : ∀ {a}{A : Set a}{x y : A} → (x ≡ y) → (y ≡ x)
_⁻¹ = ind₌ (λ x y _ → y ≡ x) (λ _ → refl) _ _

-- Composition of paths
_∙_ : ∀ {a}{A : Set a}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
_∙_ {z = z} = ind₌ (λ x y _ → y ≡ z → x ≡ z) (λ _ p → p) _ _

-- Unit laws for Composition

rup : ∀ {i}{A : Set i}{a b : A} → (p : a ≡ b) → (p ∙ refl) ≡ p
rup = ind₌ (λ _ _ p → (p ∙ refl) ≡ p) (λ _ → refl) _ _

lup : ∀ {i}{A : Set i}{a b : A} → (p : a ≡ b) → (refl ∙ p) ≡ p
lup _ = refl

-- Associativity of path composition
assoc : ∀ {i}{A : Set i}{a b c d : A} → (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) → (p ∙ (q ∙ r)) ≡ ((p ∙ q) ∙ r)
assoc {c = c} {d = d} = ind₌
  (λ _ b p → (q : b ≡ c) (r : c ≡ d) → (p ∙ q ∙ r) ≡ ((p ∙ q) ∙ r))
  (λ b → ind₌
    (λ _ c q → (r : c ≡ d) → (refl ∙ q ∙ r) ≡ ((refl ∙ q) ∙ r))
    (λ _ _ → refl) _ _)
    _ _

-- It is a familiar fact in topology that when we concatenate a path p with the
-- reversed path p ⁻¹, we don’t literally obtain a constant path (which
-- corresponds to the equality refl in type theory) — instead we have a
-- homotopy, or higher path, from p ∙ p ⁻¹ to the constant path.

there-and-back-again : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → (p ∙ p ⁻¹) ≡ refl
there-and-back-again {i} {A} {x}{y} {p} = ind₌ D d _ _ p where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = (p ∙ p ⁻¹) ≡ refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

back-and-there-again : ∀ {i}{A : Set i}{x y : A}{p : x ≡ y} → (p ⁻¹ ∙ p) ≡ refl
back-and-there-again {i} {A} {x}{y} {p} = ind₌ D d _ _ p where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y p = (p ⁻¹ ∙ p) ≡ refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

-- Paths are functor looking things.
ap : ∀ {i j} {A : Set i}{B : Set j}{x y : A}{f : A → B} → (x ≡ y) → (f x ≡ f y)
ap {i}{j} {A}{B} {x}{y}{f} p = ind₌ D d x y p where
  D : (x y : A) → (p : x ≡ y) → Set j
  D x y p = f x ≡ f y

  d : (x : A) → D x x refl
  d = λ x → refl

--
ap₂ : ∀ {i j k} {A : Set i}{B : Set j}{C : Set k}{x x′ : A}{y y′ : B}(f : A → B → C) → (x ≡ x′) → (y ≡ y′) → (f x y ≡ f x′ y′)
ap₂ f p q = ap {f = λ _ → f _ _} p ∙ ap {f = f _} q

-- The dependently typed version of `ap` takes a type family and relates its instantiations with p
transport : ∀ {i j} {A : Set i}{P : A → Set j}{x y : A} → (p : x ≡ y) → P x → P y
transport {i}{j} {A}{P} {x}{y} p = ind₌ D d x y p where
    D : (x y : A) → (p : x ≡ y) → Set j
    D x y p = P x → P y

    d : (x : A) → D x x refl
    d = λ x → id

2-11-2 : ∀ {i} {A : Set i} → (a : A) {x₁ x₂ : A} (p : x₁ ≡ x₂) (q : a ≡ x₁) → (transport p q) ≡ (q ∙ p)
2-11-2 a = ind₌
  (λ x _ p → (q : a ≡ x) → (transport {P = (λ x → a ≡ x)} p q) ≡ (q ∙ p))
  (λ _ q → rup q ⁻¹)
  _ _

-- Basically, P respects equality
path-lifting : ∀ {a p}{A : Set a}{x y : A}{P : A → Set p} → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , u)
path-lifting u = cong (λ z → z , u)

-- Look, transport works in the "upper" space too!
apd : ∀ {i} {A : Set i}{P : A → Set i}{f : (x : A) → P x}{x y : A} → (p : x ≡ y) → (transport p (f x) ≡ f y)
apd {i} {A}{P} {f}{x}{y} p = ind₌ D d x y p where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y p = transport p (f x) ≡ f y

  d : (x : A) → D x x refl
  d = λ x → refl

-- We can also fix B and make transport work like fmap with equalities.
transportconst : ∀ {i} {A : Set i}{B : Set i}{P : A → B}{x y : A} → (p : x ≡ y) → (b : B) → transport p b ≡ b
transportconst {i} {A}{B}{P} {x}{y} p b = ind₌ D d x y p where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = transport p b ≡ b

  d : (x : A) → D x x refl
  d = λ x → refl

-- Path Structure for Product Types
split-path₌ : ∀ {a b}{A : Set a}{B : Set b} → (x y : (A × B)) → (x ≡ y) → (proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y)
split-path₌ xs ys p = ap {f = proj₁} p , ap {f = proj₂} p

{-
pair₌ : ∀ {a b}{A : Set a}{B : Set b} → (x y : (A × B)) → (proj₁ x ≡ proj₁ y) × (proj₂ x ≡ proj₂ y) → (x ≡ y)
pair₌ (a₁ , b₁) (a₂ , b₂) (p , q) = {!!}
-}
