module Formalization where

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
  
-- Recall Lemma 1.12

ind₌ : ∀{a}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set) → ((x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → C x y p
ind₌ C c x y p rewrite p = c y

-- Types are higher groupoids
-- --------------------------

-- Lemma 2.1.1

-- first proof

_⁻¹ : {A : Set}{x y : A} → (x ≡ y) → (y ≡ x)
_⁻¹ {A} = λ p → ind₌ D d _ _ p where
  D : (x y : A) → x ≡ y → Set
  D = λ x y p → (y ≡ x)

  d : (x : A) → D x x refl
  d = λ x → refl

-- second proof

inv-sym : {A : Set}{x y : A} → (x ≡ y) → (y ≡ x)
inv-sym refl = refl

-- Lemma 2.1.2 & 2.1.3

-- Transitivity of equality.  i.e. paths can be concatenated (strung together)

-- First proof.  We need the type family D : Π (x, y : A) Π (p : x ≡ y) → Type.  From that we
--               produce an element d : D x x reflₓ (simply identity) then apply the induction
--               principle above to D and d.
composite : {A : Set}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite {A} {_}{_}{z} p = ind₌ D d _ _ p where
  D : (x y : A) → (p : x ≡ y) → Set
  D x y _ = y ≡ z → x ≡ z

  d : (x₁ : A) → D x₁ x₁ refl
  d _ = λ x → x

-- Second proof. We need the type family D : Π (x, y : A) Π (p : x ≡ y) → Type again.  From that
--               we produce an element d (x) : D x x reflₓ again, but rather than the identity we go a
--               step further and define E : Π (x z : A) Π (q : x ≡ z) → Type.  We then produce an
--               element e (x) : E x x reflₓ.  Induction on D d then unfolds to induction on D then E e.
composite-2 : {A : Set}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite-2 {A} {_}{_}{z} = ind₌ D (λ x x₁ q → E x x₁ q) where
  D : (x y : A) → (p : x ≡ y) → Set
  D x y _ = y ≡ z → x ≡ z
  
  E : (x z : A) → (q : x ≡ z) → Set
  E x z _ = x ≡ z

  e : (x : A) → E x x refl
  e x = refl

-- Third proof.  Everything is reflexivity you fool.  The hell did you do all that work for before?
composite-3 : {A : Set}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite-3 refl refl = refl

open import Function

-- Lemma 2.1.4

{-
lem-1 : {A : Set}{x y : A}{p : x ≡ y} → p ≡ (p ∘ refl)
lem-1-2 : {A : Set}{x y : A}{p : x ≡ y} → p ≡ (refl ∘ p)

lem-2 : {A : Set}{x y z w : A}{p : x ≡ y}{q : y ≡ z}{r : z ≡ w} → (p)⁻¹ ∘ p ≡ refl
lem-2-2 : {A : Set}{x y z w : A}{p : x ≡ y}{q : y ≡ z}{r : z ≡ w} → p ∘ (p)⁻¹ ≡ refl

lem-3 : {A : Set}{x y z w : A}{p : x ≡ y}{q : y ≡ z}{r : z ≡ w} → ((p)⁻¹)⁻¹ ≡ p
lem-4 : {A : Set}{x y z w : A}{p : x ≡ y}{q : y ≡ z}{r : z ≡ w} → p ∘ (q ∘ r) ≡ (p ∘ q) ∘ r

lem-1 = ?
lem-1-2 = ?

lem-2 = ?
lem-2-2 = ?
lem-3 = ?
lem-4 = ?
-}

-- Lemma 2.1.6

Ω : (A : Set) → {p : A} → Set
Ω A {x} = x ≡ x

_X_ : {A : Set} → Ω A → Ω A → Ω A 
refl X refl = refl

Ω² : (A : Set) → {p : A} → Set
Ω² A {x} = refl ≡ refl

transport : {A : Set}{x y : A}{P : A → Set} → (p : x ≡ y) → (P x → P y)
transport {A} {P} = {!ind₌ D d x y p!}
  where
    D : (x y : A) → (p : x ≡ y) → Set
    D x y p = P x → P y

    d : {x : A} → D x x refl
    d = λ x → id

open import Data.Product

path-lifting : ∀ {a p}{A : Set a}{x y : A}{P : A → Set p} → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , u)
path-lifting = λ {a} {p} {A} {x} {y} {P} u → cong (λ z → z , u)
