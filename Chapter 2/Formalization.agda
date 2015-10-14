{-# OPTIONS --without-K #-}

module Formalization where

open import Agda.Primitive using (lsuc)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
  
-- Recall Lemma 1.12

ind₌ : ∀{a b}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set b) → ((x : A) → C x x refl) → {x y : A} → (p : x ≡ y) → C x y p
ind₌ C c {x}{y} p rewrite p = c y

-- Types are higher groupoids
-- --------------------------

-- This is the *central* idea of HoTT.  A Type isn't just an atomic entity, it's a homotopic space.
-- An ∞-groupoid consists of
--   ∘ a collection of objects
--   ∘ a collection of morphisms between objects, and then morphisms between morphisms, and so on
--   ∘ equipped with some complex algebraic structure
--
-- a morphism at level k is called a k- morphism. Morphisms at each level have
--   ∘ identity
--   ∘ composition
--   ∘ inverse operations
--
-- which are weak in the sense that they satisfy the groupoid laws (associativity
-- of composition, identity is a unit for composition, inverses cancel) only up
-- to morphisms at the next level, and this weakness gives rise to further structure.

-- Example
--
-- Because associativity of composition of morphisms p (q r) = (p q) r is itself a higher-dimensional morphism
-- we need additional operators to talk about them.  For example:

{- Mac Lane's Pentagon
 ---------------------

 All the various ways to reassociate p (q (r s))

                                  /- ((p q) r) s -\
                                 /                 \
                      (p (q r)) s                   (p q) (r s)
                                |                   |
                                |                   |
                      p ((q r) s) ----------------- p (q (r s))

-}

-- Moreover, all of this higher groupoid structure comes automagically from the induction principle
-- on Id.

-- "Informally, the induction principle for identity types says that if we
-- construct an object (or prove a statement) which depends on an inhabitant
-- p : x == y of an identity type, 
data _==_ {i} {A : Set i} (a : A) : A → Set (lsuc i) where
  idp : a == a -- then it suffices to perform the construction (or the proof) in
               -- the special case when x and y are the same (judgmentally)
               -- and p is the reflexivity element reflx : x = x (judgmentally)

-- Lemma 2.1.1 "Paths can be reversed"

-- first proof

_⁻¹ : ∀ {i} {A : Set i}{x y : A} → (x ≡ y) → (y ≡ x)
_⁻¹ {i} {A} = λ p → ind₌ D d  p where
  D : (x y : A) → x ≡ y → Set i
  D = λ x y p → (y ≡ x)

  d : (x : A) → D x x refl
  d = λ x → refl

-- second proof

inv-sym : ∀ {i} {A : Set i}{x y : A} → (x ≡ y) → (y ≡ x)
inv-sym refl = refl

-- Lemma 2.1.2 & 2.1.3 "paths can be concatenated (strung together)"

-- First proof.  We need the type family D : Π (x, y : A) Π (p : x ≡ y) → Type.  From that we
--               produce an element d : D x x reflₓ (simply identity) then apply the induction
--               principle above to D and d.
composite : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite {i} {A} {_}{_}{z} p = ind₌ D d  p where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y _ = y ≡ z → x ≡ z

  d : (x₁ : A) → D x₁ x₁ refl
  d _ = λ x → x

-- Second proof. We need the type family D : Π (x, y : A) Π (p : x ≡ y) → Type again.  From that
--               we produce an element d (x) : D x x reflₓ again, but rather than the identity we go a
--               step further and define E : Π (x z : A) Π (q : x ≡ z) → Type.  We then produce an
--               element e (x) : E x x reflₓ.  Induction on D d then unfolds to induction on D then E e.
composite-2 : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite-2 {i} {A} {_}{_}{z} = ind₌ D d where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y _ = y ≡ z → x ≡ z

  d : (x : A) → D x x refl
  d x = ind₌ E e where
    E : (x z : A) → (q : x ≡ z) → Set i
    E x z _ = x ≡ z

    e : (x : A) → E x x refl
    e x = refl


-- Third proof.  Everything is reflexivity you fool.  The hell did you do all that work for before?
composite-3 : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite-3 refl refl = refl

--   Equality   |        Homotopy        |     ∞-Groupoid      
-- reflexivity  | constant path          | identity morphism
-- symmetry     | inversion of paths     | inverse morphism
-- transitivity | concatenation of paths | composition of morphisms

open import Function

-- Lemma 2.1.4
-- These are all propositional equalities living in the type of identity types.
-- Topologically they are paths of paths, and we can form a homotopy between them.

-- For my next trick, I will need composition of paths

-- Reflexivity right
lem-1-r : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → p ≡ (composite p refl)
lem-1-r {i} {A} {x}{y} {p} = ind₌ D d p  where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = p ≡ composite p refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl
  
-- Reflexivity left
lem-1-l : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → p ≡ (composite refl p)
lem-1-l {i} {A} {x}{y} {p} = ind₌ D d p  where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = p ≡ composite refl p

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

lem-2-l : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → composite ((p)⁻¹) p ≡ refl
lem-2-l {i} {A} {x}{y} {p} = ind₌ D d p  where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y p = composite ((p)⁻¹) p ≡ refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

lem-2-r : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → composite p ((p)⁻¹) ≡ refl
lem-2-r {i} {A} {x}{y} {p} = ind₌ D d p  where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = composite p ((p)⁻¹) ≡ refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

-- Inversion of identity
lem-3 : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → ((p)⁻¹)⁻¹ ≡ p
lem-3 {i} {A} {x}{y} {p} = ind₌ D d p  where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = ((p)⁻¹)⁻¹ ≡ p

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ _ → refl

{-
-- Transitivity of identity
lem-4 : ∀ {i} {A : Set i}{x y z w : A}{p : x ≡ y}{q : y ≡ z}{r : z ≡ w} → composite p (composite q r) ≡ composite (composite p q) r
lem-4 {i} {A} {_}{_}{z} = ind₌ D₁ d₁ where
  D₁ : (x y : A) → (x ≡ y) → Set i
  D₁ x y p = (z w : A)(q : y ≡ z)(r : z ≡ w) → composite p (composite q r) ≡ composite (composite p q) r

  d₁ : (x₁ : A) → D₁ x₁ x₁ refl
  d₁ _ = ind₌ D₂ d₂ where
    D₂ : (x z : A) → (q : x ≡ z) → Set i
    D₂ x z q = (w : A)(r : z ≡ w) → composite refl (composite q r) ≡ composite (composite refl q) r

    d₂ :  (x₂ : A) → D₂ x₂ x₂ refl
    d₂ _ = ind₌ D₃ d₃ where
       D₃ : (x w : A) → (r : x ≡ w) → Set i
       D₃ x w r = (composite refl (composite refl r)) ≡ (composite (composite refl refl) r)

       d₃ : (x₃ : A) → D₃ x₃ x₃ refl
       d₃ _ = composite refl (composite refl refl) ≡ composite (composite refl refl) refl
-}

-- Lemma 2.1.6


Ω : (A : Set) → {p : A} → Set
Ω A {x} = x ≡ x

{-
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
-}

open import Data.Product

path-lifting : ∀ {a p}{A : Set a}{x y : A}{P : A → Set p} → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , u)
path-lifting = λ {a} {p} {A} {x} {y} {P} u → cong (λ z → z , u)



