module #1 where

open import Level
open import Relation.Binary.PropositionalEquality

{-
Exercise 1.1. Given functions f : A → B and g : B → C, define their composite g ◦ f : A → C.
Show that we have h ◦ (g ◦ f ) ≡ (h ◦ g) ◦ f .
-}

-- Function composition
_∘_ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

-- Proof of associativity of composition
∘-assoc : ∀ {a b c d}{A : Set a}{B : Set b}{C : Set c}{D : Set d} →
            (h : C → D) → (g : B → C) → (f : A → B) →
            h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc _ _ _ = refl
