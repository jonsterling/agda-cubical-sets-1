{-# OPTIONS --type-in-type #-}

module Basis.Graph.Boot where

open import Basis.Prelude

record Graph : Set where
  no-eta-equality
  coinductive
  field
    ● : Set
    ∂ : ● → ● → Graph
open Graph public
