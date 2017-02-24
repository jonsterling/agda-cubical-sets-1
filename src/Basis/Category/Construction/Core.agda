module Basis.Category.Construction.Core where

open import Basis.Category.Boot
open import Basis.Category.Isomorphism
open import Basis.Globular

open ≅

Core : Category → Category
⟪ Core 𝒳 ⟫ .● = ⟪ 𝒳 ⟫ .●
⟪ Core 𝒳 ⟫ .∂ x y .● = 𝒳 ⊧ x ≅ y
⟪ Core 𝒳 ⟫ .∂ x y .∂ f g .● = 𝒳 ⊧ into f ⇔ into g
⟪ Core 𝒳 ⟫ .∂ x y .∂ f g .∂ α β = G.𝟘
Core 𝒳 .idn₀ .into = idn₀ 𝒳
Core 𝒳 .idn₀ .from = idn₀ 𝒳
Core 𝒳 .idn₀ .coh-from∘into = coh-λ 𝒳
Core 𝒳 .idn₀ .coh-into∘from = coh-λ 𝒳
Core 𝒳 .cmp₀ g f .into = cmp₀ 𝒳 (into g) (into f)
Core 𝒳 .cmp₀ g f .from = cmp₀ 𝒳 (from f) (from g)
Core 𝒳 .cmp₀ g f .coh-from∘into =
  cmp₁ 𝒳
    (cmp₁ 𝒳
      (coh-from∘into f)
      (coh-ω-ρ 𝒳
        (cmp₁ 𝒳
          (cmp₁ 𝒳
            (coh-λ 𝒳)
            (coh-ω-λ 𝒳 (coh-from∘into g)))
          (inv₁ 𝒳 (coh-α 𝒳)))))
    (coh-α 𝒳)
Core 𝒳 .cmp₀ g f .coh-into∘from =
  cmp₁ 𝒳
    (cmp₁ 𝒳
      (coh-into∘from g)
      (coh-ω-ρ 𝒳
        (cmp₁ 𝒳
          (cmp₁ 𝒳
            (coh-λ 𝒳)
            (coh-ω-λ 𝒳 (coh-into∘from f)))
          (inv₁ 𝒳 (coh-α 𝒳)))))
    (coh-α 𝒳)
Core 𝒳 .idn₁ = idn₁ 𝒳
Core 𝒳 .cmp₁ = cmp₁ 𝒳
Core 𝒳 .inv₁ = inv₁ 𝒳
Core 𝒳 .coh-λ = coh-λ 𝒳
Core 𝒳 .coh-ρ = coh-ρ 𝒳
Core 𝒳 .coh-α = coh-α 𝒳
Core 𝒳 .coh-ω = coh-ω 𝒳
