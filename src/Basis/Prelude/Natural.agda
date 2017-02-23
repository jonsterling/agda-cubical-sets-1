module Basis.Prelude.Natural where

open import Basis.Prelude.Decidable
open import Basis.Prelude.Path

module ℕ where
  open import Agda.Builtin.Nat public
    renaming (Nat to ℕ)
    renaming (suc to succ)

  _≟_ : (n₀ n₁ : ℕ) → Decidable (n₀ ≡ n₁)
  zero ≟ zero = yes refl
  zero ≟ succ _ = no λ()
  succ _ ≟ zero = no λ()
  succ n₀ ≟ succ n₁ with n₀ ≟ n₁
  … | no n₀≢n₁ = no λ { refl → n₀≢n₁ refl }
  … | yes refl = yes refl
open ℕ public
  hiding (module ℕ)
  using (ℕ)
  using (zero)
  using (succ)
  using (_+_)
  using (_-_)
