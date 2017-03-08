module Basis.Category.Construction.Setoid where

open import Basis.Category.Boot
open import Basis.Graph
open import Basis.Setoid.Boot
open import Basis.Setoid.Map

≪Setoid≫ : Category
⟪ ≪Setoid≫ ⟫ .● = Setoid
⟪ ≪Setoid≫ ⟫ .∂ 𝒳 𝒴 .● = Map 𝒳 𝒴
⟪ ≪Setoid≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .● = ∀ {x} → hom 𝒴 (ap₀ F x) (ap₀ G x)
⟪ ≪Setoid≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .∂ α β = G.𝟘
≪Setoid≫ .idn₀ {𝒳} .ap₀ x = x
≪Setoid≫ .idn₀ {𝒳} .ap₁ f = f
≪Setoid≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₀ x = ap₀ G (ap₀ F x)
≪Setoid≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₁ f = ap₁ G (ap₁ F f)
≪Setoid≫ .idn₁ {𝒳}{𝒴}{F}{x} = idn₀ 𝒴
≪Setoid≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α {x} = cmp₀ 𝒴 (β {x}) (α {x})
≪Setoid≫ .inv₁ {𝒳}{𝒴}{F}{G} α {x} = inv₀ 𝒴 (α {x})
≪Setoid≫ .coh-λ {𝒳}{𝒴}{F}{x} = idn₀ 𝒴
≪Setoid≫ .coh-ρ {𝒳}{𝒴}{F}{x} = idn₀ 𝒴
≪Setoid≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H}{x} = idn₀ 𝒵
≪Setoid≫ .coh-ω {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} α β {x} = cmp₀ 𝒵 (ap₁ G₁ (β {x})) (α {ap₀ F₀ x})
