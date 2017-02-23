module Basis.Prelude.Decidable where

open import Basis.Prelude.Initial

module Decidable where
  data Decidable (A : Set) : Set where
    no : (A → 𝟘) → Decidable A
    yes : A → Decidable A
open Decidable public
  hiding (module Decidable)
  using (Decidable)
  using (no)
  using (yes)
