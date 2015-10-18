module #5 where

open import Relation.Binary.PropositionalEquality
open import Function
open import Level

ind₌ : ∀{a b}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set b) → ((x : A) → C x x refl) → {x y : A} → (p : x ≡ y) → C x y p
ind₌ C c {x}{y} p rewrite p = c y

transport : ∀ {i} {A : Set i}{P : A → Set i}{x y : A} → (p : x ≡ y) → (P x → P y)
transport {i} {A}{P} {x}{y} p = ind₌ D d p where
    D : (x y : A) → (p : x ≡ y) → Set i
    D x y p = P x → P y

    d : (x : A) → D x x refl
    d = λ x → id
    
record IsEquiv {i j}{A : Set i}{B : Set j}(to : A → B) : Set (i ⊔ j) where
  field
    from : B → A
    iso₁ : (x : A) → from (to x) ≡ x
    iso₂ : (y : B) → to (from y) ≡ y

{-
  Exercise 2.5. Prove that the functions (2.3.6) and (2.3.7) are inverse equivalences.
-}

lem2-3-6 : ∀ {i} {A B : Set i}{x y : A} → (p : x ≡ y) → (f : A → B) → (f x ≡ f y) → (transport p (f x) ≡ f y)
lem2-3-6 p f q rewrite p = refl

lem2-3-7 : ∀ {i} {A B : Set i}{x y : A} → (p : x ≡ y) → (f : A → B) → (transport p (f x) ≡ f y) → (f x ≡ f y)
lem2-3-7 p f q rewrite p = refl

lems-is-equiv : ∀ {i} {A B : Set i}{x y : A} → (p : x ≡ y) → (f : A → B) → IsEquiv (lem2-3-6 p f)
lems-is-equiv p f = record
  { from = lem2-3-7 p f
  ; iso₁ = λ x → {!!}
  ; iso₂ = λ y → {!!}
  }


