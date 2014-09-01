module OnePointOne where

open import Level
open import Relation.Binary.PropositionalEquality

_∘_ : ∀ { a b c } {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

∘-assoc : ∀ { a b c d } {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
            (h : C → D) → (g : B → C) → (f : A → B) →
            h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc _ _ _ = refl
