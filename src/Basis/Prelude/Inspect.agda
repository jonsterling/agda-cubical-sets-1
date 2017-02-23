module Basis.Prelude.Inspect where

open import Basis.Prelude.Path

module Inspect where
  record Inspect {A : Set} {B : A → Set} (f : (a : A) → B a) (a : A) (b : B a) : Set where
    constructor [_]?
    field
      φ : f a ≡ b

  inspect : {A : Set} {B : A → Set} (f : (a : A) → B a) (a : A) → Inspect f a (f a)
  inspect f a = [ refl ]?
open Inspect public
  hiding (module Inspect)
  using (Inspect)
  using ([_]?)
  using (inspect)
