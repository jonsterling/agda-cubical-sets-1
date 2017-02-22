module Discrete where

open import Category
open import Globular
open import Prelude

ℼ : Set → Globular
ℼ X .● = X
ℼ X .∂ x y = ℼ (x ≡ y)

Discrete : Set → Category
⟪ Discrete X ⟫ = ℼ X
Discrete X .idn₀ = ≡.idn
Discrete X .cmp₀ = ≡.cmp
Discrete X .idn₁ = ≡.idn
Discrete X .cmp₁ = ≡.cmp
Discrete X .inv₁ = ≡.inv
Discrete X .cmp₀* = ≡.ap² ≡.cmp
Discrete X .coh-λ = ≡.idn
Discrete X .coh-ρ {f = refl} = ≡.idn
Discrete X .coh-α {h = refl} = ≡.idn
