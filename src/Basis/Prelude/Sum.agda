module Basis.Prelude.Sum where

open import Basis.Prelude.Function

module ⊕ where
  data _⊕_ (A B : Set) : Set where
    inl : (a : A) → A ⊕ B
    inr : (b : B) → A ⊕ B

  [_,_]
    : {A B C : Set}
    → (A → C)
    → (B → C)
    → (A ⊕ B → C)
  [ f , g ] (inl a) = f a
  [ f , g ] (inr b) = g b

  [_⊕_]
    : {X Y A B : Set}
    → (X → A)
    → (Y → B)
    → (X ⊕ Y → A ⊕ B)
  [ f ⊕ g ] = [ cmp inl f , cmp inr g ]
open ⊕ public
  hiding (module _⊕_)
  using (_⊕_)
  using (inl)
  using (inr)
  using ([_,_])
  using ([_⊕_])

module Σ where
  infixr 0 _▸_
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _▸_
    field
      fst : A
      snd : B fst
  open Σ public
  syntax Σ A (λ x → B) = Σ[ A ∋ x ] B
open Σ public
  hiding (module Σ)
  using (Σ)
  using (_▸_)
  using (fst)
  using (snd)
