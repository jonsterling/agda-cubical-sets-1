module Basis.Prelude.Terminal where

module 𝟙 where
  record 𝟙 : Set where
    constructor *

  instance
    trivial : 𝟙
    trivial = *
open 𝟙 public
  hiding (module 𝟙)
  using (𝟙)
  using (*)
