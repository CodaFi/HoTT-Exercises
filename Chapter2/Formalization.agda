{-# OPTIONS --without-K #-}

module Formalization where

open import Agda.Primitive using (lsuc)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Level

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
composite {i} {A} {_}{_}{z} p = ind₌ D d p where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y _ = y ≡ z → x ≡ z

  d : (x₁ : A) → D x₁ x₁ refl
  d _ = λ x → x

-- Second proof. We need the type family D : Π (x, y : A) Π (p : x ≡ y) → Type again.  From that
--               we produce an element d (x) : D x x reflₓ again, but rather than the identity we go a
--               step further and define E : Π (x z : A) Π (q : x ≡ z) → Type.  We then produce an
--               element e (x) : E x x reflₓ.  Induction on D d then unfolds to induction on D then E e.
composite' : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite' {i} {A} {_}{_}{z} = ind₌ D d where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y _ = y ≡ z → x ≡ z

  d : (x : A) → D x x refl
  d x = ind₌ E e where
    E : (x z : A) → (q : x ≡ z) → Set i
    E x z _ = x ≡ z

    e : (x : A) → E x x refl
    e x = refl


-- Third proof.  Everything is reflexivity you fool.  The hell did you do all that work for before?
composite'' : ∀ {i} {A : Set i}{x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
composite'' refl refl = refl

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
lem-1-r {i} {A} {x}{y} {p} = ind₌ D d p where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = p ≡ composite p refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl
  
-- Reflexivity left
lem-1-l : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → p ≡ (composite refl p)
lem-1-l {i} {A} {x}{y} {p} = ind₌ D d p where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = p ≡ composite refl p

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

lem-2-l : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → composite ((p)⁻¹) p ≡ refl
lem-2-l {i} {A} {x}{y} {p} = ind₌ D d p where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y p = composite ((p)⁻¹) p ≡ refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

lem-2-r : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → composite p ((p)⁻¹) ≡ refl
lem-2-r {i} {A} {x}{y} {p} = ind₌ D d p where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = composite p ((p)⁻¹) ≡ refl

  d : (x₁ : A) → D x₁ x₁ refl
  d = λ x → refl

-- Inversion of identity
lem-3 : ∀ {i} {A : Set i}{x y : A}{p : x ≡ y} → ((p)⁻¹)⁻¹ ≡ p
lem-3 {i} {A} {x}{y} {p} = ind₌ D d p where
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

open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat using (ℕ ; suc)

-- We need pointed sets for this part
Set• : ∀ i → Set _
Set• i = Σ (Set i) λ X → X

-- The loop space of a type is
--  - A base point
--  - A loop (reflexivity) about that point
Ω₁ : ∀ {i} → Set• i → Set• i
Ω₁ (X , x) = ((x ≡ x) , refl)

-- Construct arbitrary n-dimensional loop spaces
Ωⁿ : ∀ {i} → ℕ → Set• i → Set• _
Ωⁿ 0 x = x
Ωⁿ (suc n) x = Ωⁿ n (Ω₁ x)

-- Projects the type from an n-dimensional loop space
Ω : ∀ {i} → ℕ → {X : Set i} → X → Set i
Ω n {X} x = proj₁ (Ωⁿ n (X , x))

-- Projects the loop from an n-dimensional loop space
loop : ∀ {i} n {X : Set i}(x : X) → Ω n x
loop n {X} x = proj₂ (Ωⁿ n (X , x))

-- Composition operation on n-dimensional loop spaces
_×_ : ∀ {i} n {A : Set i}{x : A} → Ω n x → Ω n x → Ω n x
_×_ n {A} {x} x₁ x₂ = loop n x

-- 2.2.1

-- We're type theorists, so we like funtor-looking things.
-- Paths are funtor looking things.
-- We like paths
-- They respect equality and are all continuous-like
ap : ∀ {i j} {A : Set i}{B : Set j}{x y : A}{f : A → B} → (x ≡ y) → (f x ≡ f y)
ap {i}{j} {A}{B} {x}{y}{f} p = ind₌ D d p where
  D : (x y : A) → (p : x ≡ y) → Set j
  D x y p = f x ≡ f y

  d : (x : A) → D x x refl
  d = λ x → refl

ap₂ : ∀ {i j k} {A : Set i}{B : Set j}{C : Set k}{x x′ : A}{y y′ : B}(f : A → B → C) → (x ≡ x′) → (y ≡ y′) → (f x y ≡ f x′ y′)
ap₂ f p q = composite (ap {f = λ _ → f _ _} p) (ap {f = f _} q)

ap' : ∀ {i j} {A : Set i}{B : Set j}{x y : A} → (f : A → B) → ((x ≡ y) → (f x ≡ f y))
ap' f refl = refl

-- 2.3

-- The dependently typed version of `ap` takes a type family and relates its instantiations with p
transport : ∀ {i} {A : Set i}{P : A → Set i}{x y : A} → (p : x ≡ y) → (P x → P y)
transport {i} {A}{P} {x}{y} p = ind₌ D d p where
    D : (x y : A) → (p : x ≡ y) → Set i
    D x y p = P x → P y

    d : (x : A) → D x x refl
    d = λ x → id
-- Topologically, we can view transport as a "path lifting" operation
-- That is, we lift the path p to a path in the space ∑[ x ∈ A ] P(x) provided we have a
-- base point u in the lifted space.
--
-- Basically, P respects equality
path-lifting : ∀ {a p}{A : Set a}{x y : A}{P : A → Set p} → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , u)
path-lifting = λ {a} {p} {A} {x} {y} {P} u → cong (λ z → z , u)

-- Look, transport works in the "upper" space too!
apd : ∀ {i} {A : Set i}{P : A → Set i}{f : (x : A) → P x}{x y : A} → (p : x ≡ y) → (transport p (f x) ≡ f y)
apd {i} {A}{P} {f}{x}{y} p = ind₌ D d p where
  D : (x y : A) → (p : x ≡ y) → Set i
  D x y p = transport p (f x) ≡ f y

  d : (x : A) → D x x refl
  d = λ x → refl

-- By induction, it suffices to assume p is refl.  Because of course it does.
apd' : ∀ {i} {A : Set i}{P : A → Set i}{f : (x : A) → P x}{x y : A} → (p : x ≡ y) → (transport p (f x) ≡ f y)
apd' refl = refl

-- We can also fix B and make transport work like fmap with equalities.
transportconst : ∀ {i} {A : Set i}{B : Set i}{P : A → B}{x y : A} → (p : x ≡ y) → (b : B) → transport p b ≡ b
transportconst {i} {A}{B}{P} {x}{y} p b = ind₌ D d p where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = transport p b ≡ b

  d : (x : A) → D x x refl
  d = λ x → refl

{-
lem-2-3-8 : ∀ {i} {A : Set i}{B : Set i}{f : A → B}{x y : A} → (p : x ≡ y) → apd p ≡ transportconst (ap p) (f x)
lem-2-3-8 {i} {A}{B}{f} {x}{y} p = ind₌ D d p where
  D : (x y : A) → (x ≡ y) → Set i
  D x y p = apd p ≡ transportconst (f x) ∘ ap p

  d : (x : A) → D x x refl
  d = refl
-}

{-
lem-2-3-9 : ∀ {i} {A : Set i}{P : A → Set i}{x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (u : P x) → transport q (transport p u) ≡ transport (p ∘ q) u
lem-2-3-9 = ?
-}

-- Homotopies

-- Under Propositions-as-Types two functions are the same if they give the same outputs on the
-- same inputs.  Which looks like this: a type whose terms are proofs of that^
_∼_ : ∀ {a b} {A : Set a}{P : A → Set b} → (f g : (x : A) → P x) → Set (a ⊔ b)
_∼_ {a}{b} {A}{P} f g = (x : A) → f x ≡ g x

-- 2.4.2

lem-2-4-2 : ∀ {a} {A : Set a}{B : Set a} → (f : A → B) → f ∼ f
lem-2-4-2 f = λ _ → refl

lem-2-4-2' : ∀ {a} {A : Set a}{B : Set a} → (f g : A → B) → (f ∼ g) → (g ∼ f)
lem-2-4-2' f g x x₁ = sym (x x₁)


-- For any A and B, a quasi-inverse of f is a triple with
--    ∘ A way back (an inverse for the homomorphism)
--    ∘ Homotopies:
--        ⊚ α : f ∘ g ∼ id
--        ⊚ β : g ∘ f ∼ id
-- For now, because I am lazy, the presence of a quasi-inverse will count
-- as our definition of equivalence for now.  Sorry.
record IsEquiv {i j}{A : Set i}{B : Set j}(to : A → B) : Set (i ⊔ j) where
  field
    from : B → A
    iso₁ : (x : A) → from (to x) ≡ x
    iso₂ : (y : B) → to (from y) ≡ y

-- Example 2.4.7: Identity is an equivalence.
id-is-equiv : ∀ {i} (A : Set i) → IsEquiv (id {i}{A})
id-is-equiv {i} A = record
  { from = id {i}{A}
  ; iso₁ = λ _ → refl
  ; iso₂ = λ _ → refl
  }

-- Type equivalence is also an equivalence, just on the Universe because:
--    ∘ id-is-equiv works for it, therefore A ≃ A
--    ∘ With A ≃ B, we can always make B ≃ A
--    ∘ With A ≃ B and B ≃ C we have A ≃ C 
_≃_ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
A ≃ B = Σ (A → B) IsEquiv

open import Data.Product renaming (_×_ to _×p_)

split-path : ∀ {i j}{A : Set i}{B : Set j}{x y : A ×p B} → x ≡ y → (proj₁ x ≡ proj₁ y) ×p (proj₂ x ≡ proj₂ y)
split-path p = ap {f = proj₁} p , ap {f = proj₂} p

pair₌ : ∀ {i j}{A : Set i}{B : Set j}{x y : A ×p B} → (proj₁ x ≡ proj₁ y) ×p (proj₂ x ≡ proj₂ y) → x ≡ y
pair₌ (p , q) = ap₂ _,_ p q

split-is-equiv : ∀ {i j}{A : Set i}{B : Set j}{x y : A ×p B} → IsEquiv (pair₌ {x = x}{y = y})
split-is-equiv {x = x}{y = y} = record
  { from = split-path
  ; iso₁ = λ pq →
          ind₌ (λ _ _ p → ∀ {b₁ b₂} (q : b₁ ≡ b₂) →
            split-path (pair₌ (p , q)) ≡ p , q)
          (λ _ q → ind₌
            (λ _ _ q →
              split-path (pair₌ (refl , q)) ≡ refl , q)
            (λ _ → refl) q)
              (proj₁ pq) (proj₂ pq)
  ; iso₂ = ind₌ (λ _ _ p → pair₌ (split-path p) ≡ p) (λ _ → refl)
  }

{-
happly : ∀ {i}{A : Set i}{f g : A → Set i} → (f ≡ g) → ((x : A) → f x ≡ g x)
happly p x = ap' (λ u → u x)
-}

-- 2.10

-- This says, when you get down to it, id on universes is a
-- type family with a total space of pointed types.  Turns out
-- Ω isn't just for horses.
idtoeqv : ∀ {i} {A : Set i}{B : Set i} → (A ≡ B) → (A ≃ B)
idtoeqv {_}{A} refl = (id , id-is-equiv A)

-- With idtoeqv in hand, we have to ask Agda nicely to make idtoeqv an equivalence.

postulate -- Just kidding
  ua : ∀ {i} {A : Set i}{B : Set i} → (A ≃ B) ≃ (A ≡ B)
-- ^This says "equivalent types may be identified"

-- 2.12

{-
data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (x : A) → A ⊎ B
  inr : (y : B) → A ⊎ B

code : ∀ {a b}{{A : Set a}}{{B : Set b}} → A ⊎ B → Set (a ⊔ b)
code (inl a) = ?
code (inr b) = ⊥
    
code-lem : ∀ {a b}{{A : Set a}}{{B : Set b}} → (x : A ⊎ B) → (a₀ : A) → ((inl a₀ ≡ x) ≃ code x)
code-lem {{A}} {{B}} x a₀ = ? where
    encode : (x : A ⊎ B) → (p : inl a₀ ≡ x) → code x
    encode x p = transport p refl

    decode : (x : A ⊎ B) → (c : code x) → inl a₀ ≡ x
    decode x c = ?
-}

open import Data.Nat
open import Data.Unit
open import Data.Empty

code : ℕ → ℕ → Set
code ℕ.zero ℕ.zero = ⊤
code ℕ.zero (ℕ.suc m) = ⊥
code (ℕ.suc n) ℕ.zero = ⊥
code (ℕ.suc n) (ℕ.suc m) = code n m

r : (n : ℕ) → code n n
r ℕ.zero = tt
r (ℕ.suc n) = r n

-- 2.13

natcode-lem : ∀ {m n : ℕ} → (m ≡ n) → code m n
natcode-lem {x}{y} p = encode {x}{y} p where
  encode : ∀ {m n : ℕ} → (m ≡ n) → code m n
  encode {m}{n} p = transport p (r m)

  decode : ∀ {m n : ℕ} → code m n → (m ≡ n)
  decode {ℕ.zero} {ℕ.zero} tt = refl 
  decode {ℕ.zero} {ℕ.suc _} ()
  decode {ℕ.suc _} {ℕ.zero} ()
  decode {ℕ.suc m} {ℕ.suc n} c = cong ℕ.suc (decode c)

  enc-dec-quasi : ∀ {n : ℕ} → decode {n}{n} (encode {n}{n} refl) ≡ refl
  enc-dec-quasi {ℕ.zero} = refl
  enc-dec-quasi {ℕ.suc n₁} = {!!}
