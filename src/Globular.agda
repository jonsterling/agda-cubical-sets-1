{-# OPTIONS --type-in-type #-}

module Globular where

open import Prelude

record Globular : Set where
  no-eta-equality
  coinductive
  field
    ● : Set
    ∂ : ● → ● → Globular
open Globular public

Cell : Globular → Nat → Set
Cell A zero = Set
Cell A (succ zero) = (a b : ● A) → Set
Cell A (succ n) = {a b : ● A} → Cell (∂ A a b) n

cell : (A : Globular) (n : Nat) → Cell A n
cell A zero = ● A
cell A (succ zero) a b = ● (∂ A a b)
cell A (succ (succ n)) {a}{b} = cell (∂ A a b) (succ n)

module CellSyntax {A : Globular} where
  infix 0 _⇾_
  infix 0 _⇔_

  _⇾_ : Cell A 1
  _⇾_ = cell A 1
  {-# DISPLAY cell A 1 = _⇾_ #-}

  _⇔_ : Cell A 2
  _⇔_ = cell A 2
  {-# DISPLAY cell A 2 = _⇔_ #-}
