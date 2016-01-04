module Basics where

id : ∀ {a}{A : Set a} → A → A
id x = x

_∘_ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} → (f : B → C) → (g : A → B) → (A → C)
f ∘ g = λ x → f (g x)
