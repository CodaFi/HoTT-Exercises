module #5 where

open import Level
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality

{-
Exercise 1.5. Show that if we define A + B :≡ ∑(x:2) rec2(U, A, B, x), then we can give a definition
of indA+B for which the definitional equalities stated in §1.7 hold.
-}

rec₂ : ∀{c}{C : Set c} → C → C → Bool → C
rec₂ c₀ c₁ true = c₁
rec₂ c₀ c₁ false = c₀

ind₂ : ∀{c}(C : Bool → Set c) → C false → C true → (x : Bool) → C x
ind₂ C c₀ c₁ true = c₁
ind₂ C c₀ c₁ false = c₀

_⊎_ : ∀ {i} → Set i → Set i → Set _
A ⊎ B = Σ Bool λ b → if b then A else B

module SumTwo {a}{A B : Set a} where

  inl : A → A ⊎ B
  inl x = true , x

  inr : B → A ⊎ B
  inr y = false , y

  rec-sum₂ : ∀{a b c}{A : Set a}{B : A → Set b} → (C : Σ A B -> Set c) → (f : (x : A)(y : B x) → C (x , y)) → (s : Σ A B) → C s
  rec-sum₂ C f (x , y) = f x y

  ind-sum₂ : ∀{c}(C : A ⊎ B -> Set c) → ((x : A) → C (inl x)) → ((y : B) → C (inr y)) → (u : A ⊎ B) → C u
  ind-sum₂ C c₁ c₀ u = rec-sum₂ C (ind₂ (λ b → (z : if b then A else B) → C (b , z)) c₀ c₁) u 

  ind-sum₂-β₁ : ∀{c}(C : A ⊎ B -> Set c) → (f : (x : A) → C (inl x)) → (g : (y : B) → C (inr y)) → (x : A) → ind-sum₂ C f g (inl x) ≡ f x
  ind-sum₂-β₁ C f g x = refl

  ind-sum₂-β₂ : ∀{c}(C : A ⊎ B -> Set c) → (f : (x : A) → C (inl x)) → (g : (y : B) → C (inr y)) → (x : B) → ind-sum₂ C f g (inr x) ≡ g x
  ind-sum₂-β₂ C f g x = refl
