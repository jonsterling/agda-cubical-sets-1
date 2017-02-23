{-# OPTIONS --type-in-type #-}

module Basis.Globular.Boot where

open import Basis.Prelude

record Globular : Set where
  no-eta-equality
  coinductive
  field
    ● : Set
    ∂ : ● → ● → Globular
open Globular public
