module Basis.Category.Construction.Diagonal where

open import Basis.Category.Boot
open import Basis.Category.Construction.Functor
open import Basis.Category.Functor
open import Basis.Category.Transform

Diagonal : {𝒜 : Category} (𝒳 : Category) → Functor 𝒜 [ 𝒳 , 𝒜 ]
Diagonal {𝒜} 𝒳 .ap₀ a .ap₀ _ = a
Diagonal {𝒜} 𝒳 .ap₀ a .ap₁ _ = idn₀ 𝒜
Diagonal {𝒜} 𝒳 .ap₀ a .ap₂ _ = idn₁ 𝒜
Diagonal {𝒜} 𝒳 .ap₀ a .coh-idn = idn₁ 𝒜
Diagonal {𝒜} 𝒳 .ap₀ a .coh-cmp _ _ = inv₁ 𝒜 (coh-λ 𝒜)
Diagonal {𝒜} 𝒳 .ap₁ f .ap₀ _ = f
Diagonal {𝒜} 𝒳 .ap₁ f .ap₁ _ = cmp₁ 𝒜 (inv₁ 𝒜 (coh-λ 𝒜)) (coh-ρ 𝒜)
Diagonal {𝒜} 𝒳 .ap₂ α = α
Diagonal {𝒜} 𝒳 .coh-idn = idn₁ 𝒜
Diagonal {𝒜} 𝒳 .coh-cmp β α = idn₁ 𝒜
