module #15 where

{-
  Show that indiscernability of identicals follows from path induction
-}

open import Data.Product
open import Relation.Binary.PropositionalEquality

id : ∀{x}{A : Set x} → A → A
id x = x

ind₌ : ∀{a}{A : Set a} → (C : (x y : A) → (x ≡ y) → Set) → ((x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → C x y p
ind₌ C c x y p rewrite p =  c y

based-ind₌ : ∀{x}{A : Set x} → (a : A) → (C : (x : A) → (a ≡ x) → Set) → C a refl → (x : A) → (p : a ≡ x) → C x p
based-ind₌ a C c b p rewrite p = c

indiscernability-of-identicals : {A : Set}{C : A → Set} → Σ[ f ∈ ((x y : A) → (x ≡ y) → C x → C y) ]((x : A) → f x x refl ≡ id {A = C x})
indiscernability-of-identicals {A} {C} = transport , (λ _ → refl)
  where
    transport : (x y : A) → (p : x ≡ y) → C x → C y
    transport = ind₌ (λ x y _ → C x → C y) (λ x z → z)
