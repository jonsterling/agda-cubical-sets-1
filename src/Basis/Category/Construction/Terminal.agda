module Basis.Category.Construction.Terminal where

open import Basis.Category.Boot
open import Basis.Graph
open import Basis.Prelude

𝟙 : Category
⟪ 𝟙 ⟫ = G.𝟙
𝟙 .idn₀ = *
𝟙 .cmp₀ * * = *
𝟙 .idn₁ = *
𝟙 .cmp₁ * * = *
𝟙 .inv₁ * = *
𝟙 .coh-λ = *
𝟙 .coh-ρ = *
𝟙 .coh-α = *
𝟙 .coh-ω * * = *
