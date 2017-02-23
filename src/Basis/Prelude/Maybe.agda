module Basis.Prelude.Maybe where

open import Basis.Prelude.Path

module Maybe where
  data Maybe (A : Set) : Set where
    none : Maybe A
    some : A → Maybe A

  _≫=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  none ≫= f = none
  some x ≫= f = f x

  some-inj : {A : Set} {x y : A} → some x ≡ some y → x ≡ y
  some-inj refl = refl

  none≢some : {A R : Set} {a : A} → none ≡ some a → R
  none≢some ()
open Maybe public
  hiding (module Maybe)
  using (Maybe)
  using (none)
  using (some)
