module Basis.Prelude.Bool where

open import Basis.Prelude.Initial
open import Basis.Prelude.Terminal

module Bool where
  open import Agda.Builtin.Bool public

  and : Bool → Bool → Bool
  and false q = false
  and true q = q

  T : Bool → Set
  T false = 𝟘
  T true = 𝟙
open Bool public
  hiding (module Bool)
  using (Bool)
  using (false)
  using (true)
