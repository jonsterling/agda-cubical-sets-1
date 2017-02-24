module Basis.Prelude.Finite where

open import Basis.Prelude.Natural

module 𝔽 where
  data 𝔽 : ℕ → Set where
    zero : ∀ {n} → 𝔽 (succ n)
    succ : ∀ {n} (i : 𝔽 n) → 𝔽 (succ n)
open 𝔽 public
  hiding (module 𝔽)
  using (𝔽)
  using (zero)
  using (succ)
