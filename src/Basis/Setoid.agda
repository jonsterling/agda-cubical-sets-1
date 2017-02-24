module Basis.Setoid where

open import Basis.Setoid.Boot public

module S where
  open import Basis.Setoid.Boot public
  open import Basis.Setoid.Construction.Coequalizer public
  open import Basis.Setoid.Construction.Equalizer public
  open import Basis.Setoid.Construction.Hom public
  open import Basis.Setoid.Construction.Map public
  open import Basis.Setoid.Construction.Pullback public
  open import Basis.Setoid.Construction.Pushout public
  open import Basis.Setoid.Map public
open S public
  hiding (idn)
  hiding (cmp)
