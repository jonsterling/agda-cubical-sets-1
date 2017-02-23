module Basis.Prelude.String where

open import Basis.Prelude.Bool
open import Basis.Prelude.Decidable
open import Basis.Prelude.Path

module String where
  open import Agda.Builtin.String public

  private
    primitive
      primTrustMe : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y

  _≟_ : (s₀ s₁ : String) → Decidable (s₀ ≡ s₁)
  s₀ ≟ s₁ with primStringEquality s₀ s₁
  … | false = no void where postulate void : _
  … | true = yes primTrustMe
open String public
  using (String)
