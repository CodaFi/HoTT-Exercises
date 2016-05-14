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

is-ℕ-set : isSet ℕ
is-ℕ-set = λ x y p q → {!   !}

3-1-5 : ∀ {a b}{A : Set a}{B : Set b} → isSet A → isSet B → isSet (A × B)
3-1-5 SA SB x y p q = {!   !}

is-1-type : ∀ {a} → Set a → Set a
is-1-type A = (x y : A) → (p q : x ≡ y) → (r s : p ≡ q) → r ≡ s

3-1-8 : ∀ {a}{A : Set a} → isSet A → is-1-type A
3-1-8 f x y p q r s = {! (g p) ∘ r ≡ (g q)  !}
  where
    g : (q : x ≡ y) → (p ≡ q)
    g q = f x y p q

3-1-9 : ¬ (isSet Set)
3-1-9 x = remark {!   !} where
  remark : ¬ (true ≡ false)
  remark = λ ()

  e : Bool ≃ Bool
  e = e-equiv , record { from = e-equiv ; iso₁ = λ x → helper {x} ; iso₂ = λ x → helper {x} } where
    e-equiv : Bool → Bool
    e-equiv false = true
    e-equiv true = false

    helper : ∀ {x : Bool} → e-equiv (e-equiv x) ≡ x
    helper {true} = refl
    helper {false} = refl

not-double-neg : ∀ {A : Set} → (¬ (¬ A) → A) → ⊥
not-double-neg f = {!   !} where
  e : Bool ≃ Bool
  e = e-equiv , record { from = e-equiv ; iso₁ = λ x → helper {x} ; iso₂ = λ x → helper {x} } where
    e-equiv : Bool → Bool
    e-equiv true = false
    e-equiv false = true

    helper : ∀ {x : Bool} → e-equiv (e-equiv x) ≡ x
    helper {true} = refl
    helper {false} = refl

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
3-3-3 p q f g = f , record { from = g ; iso₁ = λ x → p (g (f x)) x ; iso₂ = λ y → q (f (g y)) y }

3-3-2 : ∀ {a}{P : Set a} → (p : isProp P) → (x₀ : P) → P ≃ ⊤
3-3-2 {_}{P} p x₀ = 3-3-3 p (top-is-prop) f g where
  f : P → ⊤
  f x = tt

  g : ⊤ → P
  g u = x₀


3-3-4 : ∀ {a}{A : Set a} → isProp A → isSet A
3-3-4 {_}{A} f x y p q = {!   !} {- lem p ∘ lem q ⁻¹ where
  g : _
  g = f x

  lem : (p : x ≡ y) → p ≡ g x ⁻¹ ∘ g y
  lem p = ?
-}

isProp-is-prop : ∀ {a}{A : Set a} → isProp (isProp A)
isProp-is-prop f g = funext λ x →
                     funext λ y → 3-3-4 f _ _ (f x y) (g x y)

isSet-is-prop : ∀ {a}{A : Set a} → isProp (isSet A)
isSet-is-prop f g = funext λ x →
                    funext λ y →
                    funext λ p →
                    funext λ q → 3-3-4 (f x y) _ _ (f x y p q) (g x y p q)

3-5-1 : ∀ {a}{A : Set a} → (P : A → Set) → ({x : A} → isProp (P x)) → (u v : Σ[ x ∈ A ] P x) → (proj₁ u ≡ proj₁ v) → u ≡ v
3-5-1 P x u v p = {!   !}

3-6-1 : ∀ {a b}{A : Set a}{B : Set b} → (isProp A) → (isProp B) → isProp (A × B)
3-6-1 PA PB px py = {!   !}

3-6-2 : ∀ {a b}{A : Set a}{B : A → Set b}{x : A} → (isProp (B x)) → isProp ((x : A) → B x)
3-6-2 PPI f g = funext λ x → {! f x ≡ g x  !}
