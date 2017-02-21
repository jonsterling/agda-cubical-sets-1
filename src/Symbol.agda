{-# OPTIONS --type-in-type #-}

module Symbol where

open import Category
open import Globular
open import Prelude
  hiding (¬_)
open import Setoid
  hiding (module Setoid)
  using (Setoid)

infix  1 _∈_

Symbols : Set
Symbols = List String

mutual
  data _∈_ (x : String) : Symbols → Set where
    stop
      : ∀ {xs}
      → x ∈ x ∷ xs
    step
      : ∀ {xs} y
      → (φ : x ≢ y) -- only allow refs to the first occurrence of x (shadowing)
      → (ε : x ∈ xs)
      → x ∈ y ∷ xs

  _≢_ : String → String → Set
  x ≢ y with x String.≟ y
  … | no  _ = T.𝟙
  … | yes _ = T.𝟘

record Name (X : Symbols) : Set where
  constructor pt
  field
    ▸name : String
    ▸elem : ▸name ∈ X
open Name public
