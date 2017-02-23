module Basis.Prelude.Initial where

module 𝟘 where
  infix 0 ¬_

  data 𝟘 : Set where

  ¬_ : ∀ {a} → Set a → Set a
  ¬ A = A → 𝟘

  absurd : {A : Set} → A → ¬ ¬ A
  absurd a k = k a
open 𝟘 public
  hiding (module 𝟘)
  using (𝟘)
  using (¬_)
