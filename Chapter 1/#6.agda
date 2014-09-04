module #6 where

open import Level
open import Data.Bool
open import Relation.Binary.PropositionalEquality

{-
Exercise 1.6. Show that if we define A × B :≡ ∏(x:2) rec2(U, A, B, x), then we can give a 
definition of indA×B for which the definitional equalities stated in §1.5 hold propositionally (i.e. using equality 
types). (This requires the function extensionality axiom, which is introduced in §2.9.)
-}

rec₂ : ∀{c}{C : Set c} → C → C → Bool → C
rec₂ c₀ c₁ true = c₁
rec₂ c₀ c₁ false = c₀

ind₂ : ∀{c}(C : Bool → Set c) → C false → C true → (x : Bool) → C x
ind₂ C c₀ c₁ true = c₁
ind₂ C c₀ c₁ false = c₀

_×_ : ∀ {i} → Set i → Set i → Set i
A × B = (b : Bool) → if b then A else B

module ProductTwo {a}{A B : Set a} where

  _,_ : A → B → A × B
  _,_ x y true = x
  _,_ x y false = y

  proj₁ : A × B → A
  proj₁ x = x true

  proj₂ : A × B → B
  proj₂ x = x false

  postulate
    extensionality : ∀ {a b} {A : Set a} {B : A → Set b} (f g : (a : A) → B a) → (∀ x → f x ≡ g x) → f ≡ g

  indₓ₂ : ∀{c}{C : A × B -> Set c} → (f : (x : A)(y : B) → C (x , y)) → (x : A × B) → C (proj₁ x , proj₂ x)
  indₓ₂ f x = f (proj₁ x) (proj₂ x)

-- Must use extensionality here...
  indₓ₂-β : ∀{c}{C : A × B -> Set c} → (f : (x : A)(y : B) → C (x , y)) → (x : A × B) → indₓ₂ {C = C} f x ≡ f (proj₁ x) (proj₂ x)
  indₓ₂-β f x = refl (f (lower (x false)) (lower (x true)))

