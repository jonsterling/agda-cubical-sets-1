module Basis.Syntax where

open import Basis.Prelude

infixr 1 _∘_

data ↻ : Set where

_∘_ : T.𝟘 → T.𝟘 → T.𝟘
_∘_ () ()
