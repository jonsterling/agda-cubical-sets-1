module Basis.Globular where

module G where
  open import Basis.Globular.Boot public
  open import Basis.Globular.Cell public
  open import Basis.Globular.Void public
open G public
  hiding (module Cell)
  hiding (module Globular)
  hiding (Cell)
  hiding (cell)
