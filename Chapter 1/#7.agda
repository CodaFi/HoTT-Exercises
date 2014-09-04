module #7 where

{-
Exercise 1.7. Give an alternative derivation of ind′=A from ind=A which avoids the use of universes. 
(This is easiest using concepts from later chapters.)
-}

data C : {a} (A : Set a) → (y : A) : Set a where
     _=_

ind'=A : ∀{a c}{A : Set a}(C : (x: A) → Set c)
