{-# OPTIONS --without-K #-}
module Chapter3.Formalization where

-- Sets and n-types
-- ----------------

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Relation.Nullary using (¬_)
open import Data.Bool
open import Data.Product

open import Basics
open import Relation.Equivalence.Univalence
open import Relation.Equality
open import Relation.Equality.Extensionality
open import Relation.Path.Operation


isSet : ∀ {a} → Set a → Set a
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

-- The only possible inhabitants of ⊤ is tt which means everything
-- is reflexivity.
is-1-set : isSet ⊤
is-1-set tt tt refl refl = refl

-- Ex falso quodlibet strikes again
is-0-set : isSet ⊥
is-0-set ()

hasDecEq : ∀ {i} → Set i → Set i
hasDecEq A = (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y)

decEqIsSet : ∀ {i}{A : Set i} → hasDecEq A → isSet A
decEqIsSet {A} d x y = {!   !} -- TBD: Hedberg's Theorem

-- Natural numbers are also a set because every equality type is decidable.
-- Boy, it's a pain in the ass proving that, though.
is-ℕ-set : isSet ℕ
is-ℕ-set = decEqIsSet hasDecEq-ℕ where
  hasDecEq-ℕ : hasDecEq ℕ
  hasDecEq-ℕ zero zero = inj₁ refl
  hasDecEq-ℕ zero (suc y) = inj₂ (λ ())
  hasDecEq-ℕ (suc x) zero = inj₂ (λ ())
  hasDecEq-ℕ (suc x) (suc y) with hasDecEq-ℕ x y
  hasDecEq-ℕ (suc x) (suc y) | inj₁ x₁ = inj₁ (ap {f = suc} x₁)
  hasDecEq-ℕ (suc x) (suc y) | inj₂ pnot = inj₂ (λ p → pnot (ap {f = remark} p)) where
    remark : ℕ → ℕ
    remark zero = 42
    remark (suc n) = n

is-×-set : ∀ {a b}{A : Set a}{B : Set b} → isSet A → isSet B → isSet (A × B)
is-×-set SA SB x y p q = {!   !}

is-1-type : ∀ {a} → Set a → Set a
is-1-type A = (x y : A) → (p q : x ≡ y) → (r s : p ≡ q) → r ≡ s

3-1-8 : ∀ {a}{A : Set a} → isSet A → is-1-type A
3-1-8 f x y p q r s = {! apd r  !}
  where
    g : (q : x ≡ y) → (p ≡ q)
    g q = f x y p q

3-1-9 : ¬ (isSet Set)
3-1-9 x = {!   !} where
  f : Bool → Bool
  f false = true
  f true = false

  contra : ¬ (false ≡ true)
  contra ()

  lem : IsEquiv f
  lem = record
    { from = f
    ; iso₁ = λ x → mlem {x}
    ; iso₂ = λ x → mlem {x}
    } where
    mlem : ∀ {x : Bool} → f (f x) ≡ x
    mlem {false} = refl
    mlem {true} = refl

not-double-neg : ∀ {A : Set} → (¬ (¬ A) → A) → ⊥
not-double-neg f = {!  !} where
  e : Bool ≃ Bool
  e = e-equiv , record { from = e-equiv ; iso₁ = λ x → helper {x} ; iso₂ = λ x → helper {x} } where
    e-equiv : Bool → Bool
    e-equiv true = false
    e-equiv false = true

    helper : ∀ {x : Bool} → e-equiv (e-equiv x) ≡ x
    helper {true} = refl
    helper {false} = refl

  -- 3-2-4 : (x : Bool) → ¬ (e x ≡ x)
  -- 3-2-4 = ?

  p : Bool ≡ Bool
  p = {! ua e  !}

not-lem : ∀ {A : Set} → ¬ (A ⊎ (¬ A))
not-lem {A} (inj₁ x) = not-double-neg (λ _ → x)
not-lem {A} (inj₂ w) = not-double-neg (λ x → ⊥-elim (x w))

-- This defines "mere propositions"
-- If all elements of P are connected by a path, then p contains no
-- higher homotopy.
--
-- "The adjective “mere” emphasizes that although any type may be regarded as a
-- proposition (which we prove by giving an inhabitant of it), a type that is a
-- mere proposition cannot usefully be regarded as any more than a proposition:
-- there is no additional information contained in a witness of its truth."
isProp : ∀ {a} → Set a → Set a
isProp P = (x y : P) → (x ≡ y)

top-is-prop : isProp ⊤
top-is-prop tt tt = refl

3-3-3 : ∀ {a b}{P : Set a}{Q : Set b} → (p : isProp P)(q : isProp Q) → (f : P → Q) → (g : Q → P) → P ≃ Q
3-3-3 p q f g = f , record
                      { from = g
                      ; iso₁ = λ x → p (g (f x)) x
                      ; iso₂ = λ y → q (f (g y)) y
                      }

3-3-2 : ∀ {a}{P : Set a} → (p : isProp P) → (x₀ : P) → P ≃ ⊤
3-3-2 {_}{P} p x₀ = 3-3-3 p (top-is-prop) f g where
  f : P → ⊤
  f x = tt

  g : ⊤ → P
  g u = x₀

isProp-isSet : ∀ {a}{A : Set a} → isProp A → isSet A
isProp-isSet {_}{A} f x y p q = lem p ∙ lem q ⁻¹ where
  g : (y : A) → x ≡ y
  g y = f x y

  -- Read bottom-to-top
  lem : (p : x ≡ y) → p ≡ (g x ⁻¹ ∙ g y)
  lem p = (ap {f = (λ z → z ∙ p)} (back-and-there-again {p = (g x)}) ⁻¹) -- we have p = g(x)−1   g(y) = q.
        ∙ (assoc (g x ⁻¹) (g x) p ⁻¹) -- and after a little convincing
        ∙ ap {f = (λ z → (g x ⁻¹) ∙ z)} -- which is to say that p = g(y)⁻¹ ∙ g(z)
          ( (2-11-2 x p (g x) ⁻¹) -- Hence by Lemma 2.11.2, we have g(y) ∙ p = g(z)
          ∙ (apd {f = g} p) -- we have apd(p) : p(g(y)) = g(z).
          ) -- Then for any y,z : A and p : y = z

isProp-is-prop : ∀ {a}{A : Set a} → isProp (isProp A)
isProp-is-prop f g = funext λ x →
                     funext λ y → isProp-isSet f _ _ (f x y) (g x y)

isSet-is-prop : ∀ {a}{A : Set a} → isProp (isSet A)
isSet-is-prop f g = funext λ x →
                    funext λ y →
                    funext λ p →
                    funext λ q → isProp-isSet (f x y) _ _ (f x y p q) (g x y p q)

3-5-1 : ∀ {a}{A : Set a} → (P : A → Set) → ({x : A} → isProp (P x)) → (u v : Σ[ x ∈ A ] P x) → (proj₁ u ≡ proj₁ v) → u ≡ v
3-5-1 P x u v p = {!   !}

3-6-1 : ∀ {a b}{A : Set a}{B : Set b} → (isProp A) → (isProp B) → isProp (A × B)
3-6-1 PA PB px py = {!   !}

3-6-2 : ∀ {a b}{A : Set a}{B : A → Set b}{x : A} → (isProp (B x)) → isProp ((x : A) → B x)
3-6-2 PPI f g = funext λ x → {! f x ≡ g x  !}
