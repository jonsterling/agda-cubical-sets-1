module Basis.Prelude.Product where

module ⊗ where
  infixr 0 _,_
  record _⊗_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _⊗_ public
open ⊗ public
  hiding (module _⊗_)
  using (_⊗_)
  using (_,_)
  using (fst)
  using (snd)
