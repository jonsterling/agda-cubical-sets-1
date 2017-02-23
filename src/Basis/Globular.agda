module Basis.Globular where

module G where
  open import Basis.Globular.Boot public
  open import Basis.Globular.Cell public
  open import Basis.Globular.Fundamental public
  open import Basis.Globular.Initial public
  open import Basis.Globular.Terminal public
open G public
  hiding (module Cell)
  hiding (module Globular)
  hiding (Cell)
  hiding (cell)
  hiding (𝟘)
  hiding (𝟙)
