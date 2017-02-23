module Basis.Category.Construction.Yoneda where

open import Basis.Category.Boot
open import Basis.Category.Construction.Category
open import Basis.Category.Construction.Diagonal
open import Basis.Category.Construction.Functor
open import Basis.Category.Construction.Opposite
open import Basis.Category.Construction.Presheaf
open import Basis.Category.Construction.Product
open import Basis.Category.Construction.Setoid
open import Basis.Category.Construction.Terminal
open import Basis.Category.Functor
open import Basis.Category.Transform
open import Basis.Globular
open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Hom
open import Basis.Setoid.Map
open import Basis.Prelude

≪_[-,-]≫ : ∀ 𝒳 → Functor (Op 𝒳 ⊗ 𝒳) ≪Setoid≫
≪ 𝒳 [-,-]≫ .ap₀ (x , y) =
  ≪hom≫ 𝒳 x y
≪ 𝒳 [-,-]≫ .ap₁ (f , g) .ap₀ h =
  cmp₀ 𝒳 (cmp₀ 𝒳 g h) f
≪ 𝒳 [-,-]≫ .ap₁ {x₀ , x₁}{y₀ , y₁}(f , g) .ap₁ α =
  cmp₀* 𝒳 (cmp₀* 𝒳 (idn₁ 𝒳) α) (idn₁ 𝒳)
≪ 𝒳 [-,-]≫ .ap₂ {x₀ , x₁}{y₀ , y₁}{f₀ , f₁}{g₀ , g₁} (α , β) =
  cmp₀* 𝒳 (cmp₀* 𝒳 β (idn₁ 𝒳)) α
≪ 𝒳 [-,-]≫ .coh-idn {x , y}{f} =
  cmp₁ 𝒳 (coh-λ 𝒳) (coh-ρ 𝒳)
≪ 𝒳 [-,-]≫ .coh-cmp {x₀ , y₀}{x₁ , y₁}{x₂ , y₂} (f₁ , g₁) (f₀ , g₀) {h} =
  cmp₁ 𝒳
    (cmp₀* 𝒳
      (cmp₁ 𝒳
        (coh-α 𝒳)
        (cmp₀* 𝒳
          (coh-α 𝒳)
          (idn₁ 𝒳)))
      (idn₁ 𝒳))
    (inv₁ 𝒳 (coh-α 𝒳))

≪_[-,_]≫ : ∀ 𝒳 → ⟪ 𝒳 ⟫ .● → Functor (Op 𝒳) ≪Setoid≫
≪ 𝒳 [-, y ]≫ =
  cmp₀ ≪Category≫
    ≪ 𝒳 [-,-]≫
    ⟨ idn₀ ≪Category≫ , ap₀ (Diagonal (Op 𝒳)) y ⟩

≪_∘-≫₁
  : {𝒳 : Category} {y z : ⟪ 𝒳 ⟫ .●}
  → (g : 𝒳 ⊧ y ⇾ z)
  → Transform ≪ 𝒳 [-, y ]≫ ≪ 𝒳 [-, z ]≫
≪_∘-≫₁ {𝒳} g .ap₀ x = ≪ g ∘-≫₀
≪_∘-≫₁ {𝒳} g .ap₁ f =
  cmp₁ 𝒳
    (cmp₀* 𝒳
      (cmp₁ 𝒳
        (cmp₁ 𝒳
          (coh-α 𝒳)
          (cmp₀* 𝒳
            (cmp₁ 𝒳
              (inv₁ 𝒳 (coh-λ 𝒳))
              (coh-ρ 𝒳))
            (idn₁ 𝒳)))
        (inv₁ 𝒳 (coh-α 𝒳)))
      (idn₁ 𝒳))
    (inv₁ 𝒳 (coh-α 𝒳))

Yoneda : (𝒳 : Category) → Functor 𝒳 (≪Presheaf≫ 𝒳)
Yoneda 𝒳 .ap₀ y = ≪ 𝒳 [-, y ]≫
Yoneda 𝒳 .ap₁ g = ≪ g ∘-≫₁
Yoneda 𝒳 .ap₂ α = cmp₀* 𝒳 α (idn₁ 𝒳)
Yoneda 𝒳 .coh-idn = coh-λ 𝒳
Yoneda 𝒳 .coh-cmp g f = coh-α 𝒳
