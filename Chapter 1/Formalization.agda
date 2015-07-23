module Formalization where

module Introduction where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

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
       → Σ[ f ∈ ((x : A) → B x) ](∀ (x : A) → (R x (f x))) -- then ∃ f : A → B s.t. ∀ x : A we have R (x, f(x))
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

ind₁ : {C : ⊤ → Set} → C tt → (x : ⊤) → C x
ind₁ c ⋆ = c

-- "Induction enables us to prove the propositional uniqueness principle for 1, which asserts that its
-- only inhabitant is ⋆. That is, we can construct"

upun : (x : ⊤) → x ≡ tt
upun x = refl

-- The uniqueness of unit can also be asserted by induction

upun-ind : (x : ⊤) → x ≡ tt
upun-ind x = ind₁ {C = λ x → x ≡ tt} refl x

-- Sigma (Dependent Pair) Types 
-- ----------------------------

-- We'll use the Σ in the Agda Stdlib (because of the cool syntax).
--
-- For a constant type B rather than a B indexed by x : A, dependent pairs
-- and just cartesian products.  With that in mind, the recursor for dependent
-- pairs looks much the same as the one for the cartesian product

recₚ : ∀{a b c}{A : Set a}{B : A → Set b}{C : Set c}
     → ((x : A) → B x → C) -- It suffices to define the dependent function g such that
     → Σ[ x ∈ A ](B x) → C -- ∀ Σ(x : A)B x, C holds.
recₚ g (a , b) = g a b

-- Here's Induction

indₚ : ∀{a b c}{A : Set a}{B : A → Set b}{C : Σ[ x ∈ A ](B x) → Set c}
     → ((x : A)(y : B x) -- ∀ x , y
     → C (x , y)) -- and a property that holds for the pair (x , y)
     → (p : Σ[ x ∈ A ](B x)) → C p -- ∀ pairs x, C holds
indₚ g (a , b) = g a b


-- NB: Read Π as "forall" and Σ as "exists"

record Magma (A : Set) : Set where
  field
    mop : A → A → A
open Magma {{...}} public

record PointedMagma (A : Set) : Set where
  field
    mbasepoint : A
    pmop : (A → A → A)
  pointedMagmaIsMagma : Magma A
  pointedMagmaIsMagma = record { mop = pmop }
open PointedMagma {{...}} public

-- Coproducts

open import Data.Sum

rec₊ : ∀{a b c}{A : Set a}{B : Set b}{C : Set c} → (A → C) → (B → C) → A ⊎ B → C
rec₊ g₀ g₁ (inj₁ x) = g₀ x
rec₊ g₀ g₁ (inj₂ y) = g₁ y

-- Oh look, ⊥

open import Data.Empty

-- Any definition of the recursor would means proving 'ex falso quodlibet'.
-- Let's try not to do that...
rec₀ : ∀{c}{C : Set c} → ⊥ → C
rec₀ ()

ind₊ :  ∀{a b c}{A : Set a}{B : Set b}{C : (A ⊎ B) → Set c}
     → ((x : A) → C (inj₁ x))
     → ((y : B) → C (inj₂ y))
     → (x : A ⊎ B) → C x
ind₊ g₀ g₁ (inj₁ x) = g₀ x
ind₊ g₀ g₁ (inj₂ y) = g₁ y

ind₀ : ∀{c}{C : ⊥ → Set c} → (z : ⊥) → C z
ind₀ ()

-- The type of booleans

open import Data.Bool

rec₂ : ∀{c}{C : Set c} → C → C → Bool → C
rec₂ c₀ c₁ true = c₁
rec₂ c₀ c₁ false = c₀

ind₂ : ∀{c}{C : Bool → Set c} → C false → C true → (x : Bool) → C x
ind₂ c₀ c₁ true = c₁
ind₂ c₀ c₁ false = c₀

dec₂ : (x : Bool) → (x ≡ false) ⊎ (x ≡ true)
dec₂ x = ind₂ {C = λ x → (x ≡ false) ⊎ (x ≡ true)} (inj₁ refl) (inj₂ refl) x

-- The type of Natural Numbers

open import Data.Nat

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

add : ℕ → ℕ → ℕ
add zero n = n
add (suc m) n = suc (add m n)

recₙ : ∀{c}{C : Set c} → C → (ℕ → C → C) → ℕ → C
recₙ c₀ cₛ zero = c₀
recₙ c₀ cₛ (suc n) = cₛ n (recₙ c₀ cₛ n)

double-recₙ : ℕ → ℕ
double-recₙ = recₙ 0 (λ n y → suc (suc y))

add-recₙ : ℕ → ℕ → ℕ
add-recₙ = recₙ {C = ℕ → ℕ} (λ n → n) (λ n → λ g m → suc (g m))

indₙ : {C : ℕ → Set} → C 0 → ((n : ℕ) → C n → C (suc n)) → (n : ℕ) → C n
indₙ c₀ cₛ zero = c₀
indₙ c₀ cₛ (suc n) = cₛ n (indₙ c₀ cₛ n)

assoc : (i j k : ℕ) → i + (j + k) ≡ (i + j) + k
assoc = indₙ {C = λ i → (j k : ℕ) → i + (j + k) ≡ (i + j) + k} assoc₀ assocₛ
  where
    assoc₀ : (j k : ℕ) → 0 + (j + k) ≡ (0 + j) + k
    assoc₀ j k = refl

    assocₛ : (i : ℕ) → ((j k : ℕ) → i + (j + k) ≡ (i + j) + k) → (j k : ℕ) → (suc i) + (j + k) ≡ ((suc i) + j) + k
    assocₛ _ i j k = cong suc (i j k)

-- Propositions As Types

{-
¬_ : {A : Set} → A → ⊥
¬ x = ()
-}


-- Path Induction

open import Level

ind₌ : ∀{a}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set) → ((x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → C x y p
ind₌ C c x y p rewrite p =  c y

based-ind₌ : ∀{x}{A : Set x} → (a : A) → (C : (x : A) → (a ≡ x) → Set) → C a refl → (x : A) → (p : a ≡ x) → C x p
based-ind₌ a C c b p rewrite p = c

{-
data D {w}{A : Set w} : (x y : A) → (x ≡ y) → Set w where
  mkD : (x y : A) → (p : x ≡ y) → (C : (z : A) → (x ≡ z) → Set) → C x refl → C y p → D x y p

ind₌-β : ∀{a}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set) → (c : (x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → ind₌ C c x y p ≡ based-ind₌ x (C x) (c x) y p
ind₌-β C c x y p = {!!}
  where
    d : ∀{a}{A : Set a} → (x : A) → D x x refl
    d = λ x₁ → {!!}
-}
