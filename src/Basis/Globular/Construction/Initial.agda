module Basis.Globular.Construction.Initial where

open import Basis.Globular.Boot
open import Basis.Prelude

𝟘 : Globular
𝟘 .● = T.𝟘
𝟘 .∂ _ _ = 𝟘
