module Basis.Prelude.Sum where

module ⊕ where
  data _⊕_ (A B : Set) : Set where
    inl : (a : A) → A ⊕ B
    inr : (b : B) → A ⊕ B
open ⊕ public
  hiding (module _⊕_)
  using (_⊕_)
  using (inl)
  using (inr)

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
