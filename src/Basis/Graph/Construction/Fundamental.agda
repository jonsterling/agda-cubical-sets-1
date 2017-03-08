module Basis.Graph.Construction.Fundamental where

open import Basis.Graph.Boot
open import Basis.Prelude

ℼ : Set → Graph
ℼ X .● = X
ℼ X .∂ x y = ℼ (x ≡ y)
