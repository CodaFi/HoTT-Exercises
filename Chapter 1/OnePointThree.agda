module OnePointThree where

open import OnePointTwo as Two
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

module Product { a b c }{A : Set a}{B : Set b}{C : Set c}(g : A → B → C) where

  uppt : (x : A × B) → (proj₁ x , proj₂ x) ≡ x
  uppt = λ x → refl

  indₓ : ∀{k}(P : A × B → Set k) → ((x : A)(y : B) → P (x , y)) → (x : A × B) → P x
  indₓ P f x = subst P (uppt x) (f (proj₁ x) (proj₂ x))

  indₓ-β : ∀{k}(P : A × B → Set k) → (f : (x : A)(y : B) → P (x , y)) → (x : A)(y : B) → indₓ P f (x , y) ≡ f x y
  indₓ-β P f x y = refl

module Sum { a b c }{A : Set a}{B : A → Set b}{C : Set c}(g : (x : A) → B x → C) where

  uppt : (x : Σ A B) → (proj₁ x , proj₂ x) ≡ x 
  uppt = λ x → refl

  ind-Σ : ∀{k}(C : Σ A B → Set k) → ((a : A)(b : B a) → C (a , b)) → (p : Σ A B) → C p
  ind-Σ C f x = subst C (uppt x) (f (proj₁ x) (proj₂ x))

  ind-Σ-β : ∀{k}(C : Σ A B → Set k) → (f : (a : A)(b : B a) → C (a , b)) → (x : A)(y : B x) → ind-Σ C f (x , y) ≡ f x y
  ind-Σ-β C f x y = refl 
