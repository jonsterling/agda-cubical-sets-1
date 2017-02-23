module Basis.Globular.Fundamental where

open import Basis.Globular.Boot
open import Basis.Prelude

ℼ : Set → Globular
ℼ X .● = X
ℼ X .∂ x y = ℼ (x ≡ y)
