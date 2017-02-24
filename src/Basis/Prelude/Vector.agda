module Basis.Prelude.Vector where

open import Basis.Prelude.Finite
open import Basis.Prelude.Natural

module Vector where
  data Vector (A : Set) : ℕ → Set where
    [] : Vector A 0
    _∷_ : ∀ {n} (x : A) (xs : Vector A n) → Vector A (succ n)

  look : ∀ {A n} → Vector A n → (𝔽 n → A)
  look (x ∷ xs) zero = x
  look (x ∷ xs) (succ i) = look xs i
open Vector public
  using ([])
  using (_∷_)
