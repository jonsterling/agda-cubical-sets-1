module Basis.Category.Construction.Initial where

open import Basis.Category.Boot
open import Basis.Globular
open import Basis.Prelude

𝟘 : Category
⟪ 𝟘 ⟫ = G.𝟘
𝟘 .idn₀ {()}
𝟘 .cmp₀ {()}
𝟘 .idn₁ {()}
𝟘 .cmp₁ {()}
𝟘 .inv₁ {()}
𝟘 .cmp₀* {()}
𝟘 .coh-λ {()}
𝟘 .coh-ρ {()}
𝟘 .coh-α {()}
