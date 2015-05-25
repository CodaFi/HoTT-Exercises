module OnePointFourteen where

{-
  Why do the induction principles for identity types not allow us to construct a
  function f : ∏(x:A) ∏(p:x=x) (p = refl[x]) with the defining equation
              f(x,refl[x]) :≡ refl[refl[x]]   ?
-}

{-
  To use induction here we need proof that refl x ≡ p then use refl as a relation to prove
  that refl x ≡ p again.  It's a circular construction.
-}

open import Relation.Binary.PropositionalEquality

{- Closest I could get this into Agda.  Does not compile.
f : {A : Set} → (x : A) → (p : x ≡ x) → p ≡ refl x
f x (refl x) = refl (refl x)
-}
