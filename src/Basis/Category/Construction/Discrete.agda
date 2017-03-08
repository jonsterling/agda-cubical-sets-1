module Basis.Category.Construction.Discrete where

open import Basis.Category.Boot
open import Basis.Graph
open import Basis.Prelude

Discrete : Set → Category
⟪ Discrete X ⟫ = ℼ X
Discrete X .idn₀ = ≡.idn
Discrete X .cmp₀ = ≡.cmp
Discrete X .idn₁ = ≡.idn
Discrete X .cmp₁ = ≡.cmp
Discrete X .inv₁ = ≡.inv
Discrete X .coh-λ = ≡.idn
Discrete X .coh-ρ {f = refl} = ≡.idn
Discrete X .coh-α {h = refl} = ≡.idn
Discrete X .coh-ω = ≡.ap² ≡.cmp
