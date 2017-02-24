module Basis.Prelude.Product where

open import Basis.Prelude.Function

module ⊗ where
  infixr 0 _,_
  infixr 2 _⊗_
  record _⊗_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _⊗_ public

  ⟨_,_⟩
    : {A B C : Set}
    → (C → A)
    → (C → B)
    → (C → A ⊗ B)
  ⟨ f , g ⟩ x = f x , g x

  ⟨_⊗_⟩
    : {X Y A B : Set}
    → (X → A)
    → (Y → B)
    → (X ⊗ Y → A ⊗ B)
  ⟨ f ⊗ g ⟩ = ⟨ cmp f fst , cmp g snd ⟩
open ⊗ public
  hiding (module _⊗_)
  using (_⊗_)
  using (_,_)
  using (fst)
  using (snd)
  using (⟨_,_⟩)
  using (⟨_⊗_⟩)
