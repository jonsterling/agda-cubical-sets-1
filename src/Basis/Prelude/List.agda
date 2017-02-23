module Basis.Prelude.List where

module List where
  open import Agda.Builtin.List public
open List public
  hiding (module List)
  using (List)
  using ([])
  using (_∷_)
