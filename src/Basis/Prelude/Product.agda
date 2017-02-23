module Basis.Prelude.Product where

module ⊗ where
  infixr 0 _,_
  record _⊗_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _⊗_ public

  ⟨_,_⟩
    : {X Y Z : Set}
    → (X → Y)
    → (X → Z)
    → (X → Y ⊗ Z)
  ⟨ f , g ⟩ x = f x , g x
open ⊗ public
  hiding (module _⊗_)
  using (_⊗_)
  using (_,_)
  using (fst)
  using (snd)
  using (⟨_,_⟩)
