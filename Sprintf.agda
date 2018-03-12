{-
  [sprintf]-like mechanism
-}

open import Data.Bool
open import Data.Char
open import Data.String renaming (_++_ to _++ₛ_)
open import Data.List renaming (_++_ to _++ₗ_)

module Sprintf where

record Printable (A : Set) : Set where
  {- If the boolean is true, parenthesize -}
  field
    print-p : Bool → A → String

  print : A → String
  print = print-p false

  print-P : A → String
  print-P = print-p true

open Printable {{…}} public

data ListPrintable : Set₁ where
  [] : ListPrintable
  _∷_ : {A : Set} {{_ : Printable A}} → A → ListPrintable → ListPrintable
  [_]∷_ : {A : Set} {{_ : Printable A}} → A → ListPrintable → ListPrintable

private
  split : String → List String
  split l = split-aux (toList l) [] []  where
    -- The first argument is the list we’re splitting.
    -- The second argument is the current fragment we’re building.
    -- The third argument is the list of fragments built so far.
    split-aux : List Char → List Char → List String → List String
    split-aux [] l k = k ++ₗ (fromList l ∷ [])
    split-aux ('%' ∷ 'k' ∷ cs) l k = split-aux cs [] (k ++ₗ (fromList l ∷ []))
    split-aux (c ∷ cs) l k = split-aux cs (l ++ₗ (c ∷ [])) k

sprintf : String → ListPrintable → String
sprintf s l = sprintf-aux (split s) l  where

  sprintf-aux : List String → ListPrintable → String
  sprintf-aux (s ∷ []) [] = s
  sprintf-aux (s ∷ ss) (a ∷ as) = s ++ₛ print a ++ₛ sprintf-aux ss as
  sprintf-aux (s ∷ ss) ([ a ]∷ as) = s ++ₛ print-P a ++ₛ sprintf-aux ss as
  sprintf-aux _ _ = "Error"