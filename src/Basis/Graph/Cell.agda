{-# OPTIONS --type-in-type #-}

module Basis.Graph.Cell where

open import Basis.Graph.Boot
open import Basis.Prelude

module Cell where
  Cell : Graph → ℕ → Set
  Cell A zero = Set
  Cell A (succ zero) = (a b : ● A) → Set
  Cell A (succ n) = {a b : ● A} → Cell (∂ A a b) n

  cell : (A : Graph) (n : ℕ) → Cell A n
  cell A zero = ● A
  cell A (succ zero) a b = ● (∂ A a b)
  cell A (succ (succ n)) {a}{b} = cell (∂ A a b) (succ n)

  module Syntax {A : Graph} where
    infix 0 _⇾_
    infix 0 _⇔_

    _⇾_ : Cell A 1
    _⇾_ = cell A 1
    {-# DISPLAY cell A 1 = _⇾_ #-}

    _⇔_ : Cell A 2
    _⇔_ = cell A 2
    {-# DISPLAY cell A 2 = _⇔_ #-}
open Cell public
  using (Cell)
  using (cell)
