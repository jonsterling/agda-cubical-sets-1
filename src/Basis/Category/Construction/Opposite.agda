module Basis.Category.Construction.Opposite where

open import Basis.Category.Boot
open import Basis.Globular

Op : Category → Category
⟪ Op 𝒳 ⟫ .● = ● ⟪ 𝒳 ⟫
⟪ Op 𝒳 ⟫ .∂ x y .● = ⟪ 𝒳 ⟫ .∂ y x .●
⟪ Op 𝒳 ⟫ .∂ x y .∂ f g .● = ⟪ 𝒳 ⟫ .∂ y x .∂ f g .●
⟪ Op 𝒳 ⟫ .∂ x y .∂ f g .∂ α β = ⟪ 𝒳 ⟫ .∂ y x .∂ f g .∂ α β
Op 𝒳 .idn₀ = idn₀ 𝒳
Op 𝒳 .cmp₀ g f = cmp₀ 𝒳 f g
Op 𝒳 .idn₁ = idn₁ 𝒳
Op 𝒳 .cmp₁ = cmp₁ 𝒳
Op 𝒳 .inv₁ = inv₁ 𝒳
Op 𝒳 .cmp₀* α β = cmp₀* 𝒳 β α
Op 𝒳 .coh-λ = coh-ρ 𝒳
Op 𝒳 .coh-ρ = coh-λ 𝒳
Op 𝒳 .coh-α = inv₁ 𝒳 (coh-α 𝒳)
