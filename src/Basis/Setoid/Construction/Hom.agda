module Basis.Setoid.Construction.Hom where

open import Basis.Category.Boot
open import Basis.Globular
open import Basis.Setoid.Boot
open import Basis.Setoid.Map

≪hom≫ : (𝒳 : Category) (x y : ⟪ 𝒳 ⟫ .●) → Setoid
≪hom≫ 𝒳 x y .obj = ⟪ 𝒳 ⟫ .∂ x y .●
≪hom≫ 𝒳 x y .hom f g = ⟪ 𝒳 ⟫ .∂ x y .∂ f g .●
≪hom≫ 𝒳 x y .idn₀ {f} = idn₁ 𝒳
≪hom≫ 𝒳 x y .cmp₀ {f}{g}{h} = cmp₁ 𝒳
≪hom≫ 𝒳 x y .inv₀ {f}{g} = inv₁ 𝒳

≪-∘_≫₀
  : {𝒳 : Category} {x y z : ⟪ 𝒳 ⟫ .●}
  → (f : 𝒳 ⊧ x ⇾ y)
  → Map (≪hom≫ 𝒳 y z) (≪hom≫ 𝒳 x z)
≪-∘_≫₀ {𝒳} f .ap₀ g = cmp₀ 𝒳 g f
≪-∘_≫₀ {𝒳} f .ap₁ {g₀}{g₁} β = coh-ω-λ 𝒳 β

≪_∘-≫₀
  : {𝒳 : Category} {x y z : ⟪ 𝒳 ⟫ .●}
  → (g : 𝒳 ⊧ y ⇾ z)
  → Map (≪hom≫ 𝒳 x y) (≪hom≫ 𝒳 x z)
≪_∘-≫₀ {𝒳} g .ap₀ f = cmp₀ 𝒳 g f
≪_∘-≫₀ {𝒳} g .ap₁ {f₀}{f₁} α = coh-ω-ρ 𝒳 α
