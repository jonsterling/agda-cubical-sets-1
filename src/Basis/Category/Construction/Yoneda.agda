module Basis.Category.Construction.Yoneda where

open import Basis.Category.Boot
open import Basis.Category.Construction.Category
open import Basis.Category.Construction.Diagonal
open import Basis.Category.Construction.Functor
open import Basis.Category.Construction.Opposite
open import Basis.Category.Construction.Presheaf
open import Basis.Category.Construction.Product
open import Basis.Category.Construction.Profunctor
open import Basis.Category.Construction.Setoid
open import Basis.Category.Construction.Terminal
open import Basis.Category.Functor
open import Basis.Category.Transform
open import Basis.Globular
open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Hom
open import Basis.Setoid.Map
open import Basis.Prelude

≪_[-,_]≫
  : ∀ 𝒳
  → ● ⟪ 𝒳 ⟫
  → Functor (Op 𝒳) ≪Setoid≫
≪ 𝒳 [-, y ]≫ .ap₀ x = ≪hom≫ 𝒳 x y
≪ 𝒳 [-, y ]≫ .ap₁ f = ≪-∘ f ≫₀
≪ 𝒳 [-, y ]≫ .ap₂ α = coh-ω-ρ 𝒳 α
≪ 𝒳 [-, y ]≫ .coh-idn = coh-ρ 𝒳
≪ 𝒳 [-, y ]≫ .coh-cmp g f = inv₁ 𝒳 (coh-α 𝒳)

≪_∘-≫₁
  : {𝒳 : Category} {y z : ⟪ 𝒳 ⟫ .●}
  → (g : 𝒳 ⊧ y ⇾ z)
  → Transform ≪ 𝒳 [-, y ]≫ ≪ 𝒳 [-, z ]≫
≪_∘-≫₁ {𝒳} g .ap₀ x = ≪ g ∘-≫₀
≪_∘-≫₁ {𝒳} g .ap₁ f = inv₁ 𝒳 (coh-α 𝒳)

Yoneda : (𝒳 : Category) → Functor 𝒳 (≪Presheaf≫ 𝒳)
Yoneda 𝒳 .ap₀ y = ≪ 𝒳 [-, y ]≫
Yoneda 𝒳 .ap₁ g = ≪ g ∘-≫₁
Yoneda 𝒳 .ap₂ α = coh-ω-λ 𝒳 α
Yoneda 𝒳 .coh-idn = coh-λ 𝒳
Yoneda 𝒳 .coh-cmp g f = coh-α 𝒳
