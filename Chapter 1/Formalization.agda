module Formalization where

id : ∀{a}{A : Set a} → A → A
id x = x

swap : ∀{a b c}{A : Set a}{B : Set b}{C : Set c} → (A → B → C) → (B → A → C)
swap g = λ z z₁ → g z₁ z

module 1-5 {a b c}{A : Set a}{B : Set b}{C : Set c}(g : A → B → C) where

  open import Level hiding (zero)
  open import Relation.Binary.PropositionalEquality

  data ⊤ : Set where
    * : ⊤

  record ∏ {a b}(A : Set a)(B : Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B

  f : ∏ A B → C
  f p = g (∏.proj₁ p) (∏.proj₂ p)

  f-β : (x : A)(y : B) → f (x , y) ≡ g x y
  f-β x y = refl

  recₓ : ∀{k}(C : Set k)(g : A → B → C) → (x : A)(y : B) → C
  recₓ C g a b = g a b

  pr₁-β : (x : A)(y : B) → recₓ A (λ a → λ b → a) x y ≡ ∏.proj₁ (x , y) 
  pr₁-β x y = refl

  pr₂-β : (x : A)(y : B) → recₓ B (λ a → λ b → b) x y ≡ ∏.proj₂ (x , y) 
  pr₂-β x y = refl

{-
  rec₁ : ∀{k}(K : Set k) → ⊤ → C
  rec₁ K c t = c
-}

  uppt : (x : ∏ A B) → x ≡ (∏.proj₁ x ,  ∏.proj₂ x)
  uppt x = refl

  ind-× : ∀{c}(C : ∏ A B → Set c) → ((x : A)(y : B) → C (x , y)) → (x : A)(y : B) → C (x , y)
  ind-× C g x y = g x y


