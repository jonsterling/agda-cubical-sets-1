module Basis.Category.Construction.Functor where

open import Basis.Category.Boot
open import Basis.Category.Functor
open import Basis.Category.Transform
open import Basis.Graph

≪Functor≫ : Category → Category → Category
⟪ ≪Functor≫ 𝒳 𝒴 ⟫ .● = Functor 𝒳 𝒴
⟪ ≪Functor≫ 𝒳 𝒴 ⟫ .∂ F G .● = Transform F G
⟪ ≪Functor≫ 𝒳 𝒴 ⟫ .∂ F G .∂ α β .● = ∀ {x} → 𝒴 ⊧ ap₀ α x ⇔ ap₀ β x
⟪ ≪Functor≫ 𝒳 𝒴 ⟫ .∂ F G .∂ α β .∂ 𝔭 𝔮 = G.𝟘
≪Functor≫ 𝒳 𝒴 .idn₀ .ap₀ x = idn₀ 𝒴
≪Functor≫ 𝒳 𝒴 .idn₀ {F} .ap₁ {x}{y} f = cmp₁ 𝒴 (inv₁ 𝒴 (coh-ρ 𝒴)) (coh-λ 𝒴)
≪Functor≫ 𝒳 𝒴 .cmp₀ {F}{G}{H} β α .ap₀ x = cmp₀ 𝒴 (ap₀ β x) (ap₀ α x)
≪Functor≫ 𝒳 𝒴 .cmp₀ {F}{G}{H} β α .ap₁ {x}{y} f =
  cmp₁ 𝒴
    (cmp₁ 𝒴
      (cmp₁ 𝒴
        (cmp₁ 𝒴
          (coh-α 𝒴)
          (coh-ω-λ 𝒴 (ap₁ β f)))
        (inv₁ 𝒴 (coh-α 𝒴)))
      (coh-ω-ρ 𝒴 (ap₁ α f)))
    (coh-α 𝒴)
≪Functor≫ 𝒳 𝒴 .idn₁ {F}{G}{α}{x} = idn₁ 𝒴
≪Functor≫ 𝒳 𝒴 .cmp₁ {F}{G}{α}{β}{γ} q p {x} = cmp₁ 𝒴 (q {x}) (p {x})
≪Functor≫ 𝒳 𝒴 .inv₁ {F}{G}{α}{β} p {x} = inv₁ 𝒴 (p {x})
≪Functor≫ 𝒳 𝒴 .coh-λ {F}{G}{α}{x} = coh-λ 𝒴
≪Functor≫ 𝒳 𝒴 .coh-ρ {F}{G}{α}{x} = coh-ρ 𝒴
≪Functor≫ 𝒳 𝒴 .coh-α {F}{G}{H}{I}{α}{β}{γ}{x} = coh-α 𝒴
≪Functor≫ 𝒳 𝒴 .coh-ω {F}{G}{H}{α₀}{α₁}{β₀}{β₁} q p {x} = coh-ω 𝒴 (q {x}) (p {x})
