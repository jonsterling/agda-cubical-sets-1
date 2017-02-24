module Basis.Globular where

module G where
  open import Basis.Globular.Boot public
  open import Basis.Globular.Cell public
  open import Basis.Globular.Construction.Fundamental public
  open import Basis.Globular.Construction.Initial public
  open import Basis.Globular.Construction.Product public
  open import Basis.Globular.Construction.Terminal public
open G public
  hiding (module Cell)
  hiding (module Globular)
  hiding (Cell)
  hiding (cell)
  hiding (𝟘)
  hiding (_⊗_)
  hiding (𝟙)
