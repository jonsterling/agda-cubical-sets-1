module Basis.Graph.Construction.Initial where

open import Basis.Graph.Boot
open import Basis.Prelude

𝟘 : Graph
𝟘 .● = T.𝟘
𝟘 .∂ _ _ = 𝟘
