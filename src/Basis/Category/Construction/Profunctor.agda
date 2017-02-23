module Basis.Category.Construction.Profunctor where

open import Basis.Category.Boot
open import Basis.Category.Construction.Functor
open import Basis.Category.Construction.Opposite
open import Basis.Category.Construction.Product
open import Basis.Category.Construction.Setoid
open import Basis.Category.Functor
open import Basis.Category.Transform
open import Basis.Globular
open import Basis.Prelude
open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Hom
open import Basis.Setoid.Map

Profunctor : Category → Category → Set
Profunctor 𝒳 𝒴 = Functor (Op 𝒳 ⊗ 𝒴) ≪Setoid≫

≪_[-,-]≫ : ∀ 𝒳 → Profunctor 𝒳 𝒳
≪ 𝒳 [-,-]≫ .ap₀ (x , y) = ≪hom≫ 𝒳 x y
≪ 𝒳 [-,-]≫ .ap₁ (f , g) .ap₀ h = cmp₀ 𝒳 (cmp₀ 𝒳 g h) f
≪ 𝒳 [-,-]≫ .ap₁ (f , g) .ap₁ α = cmp₀* 𝒳 (cmp₀* 𝒳 (idn₁ 𝒳) α) (idn₁ 𝒳)
≪ 𝒳 [-,-]≫ .ap₂ (α , β) = cmp₀* 𝒳 (cmp₀* 𝒳 β (idn₁ 𝒳)) α
≪ 𝒳 [-,-]≫ .coh-idn = cmp₁ 𝒳 (coh-λ 𝒳) (coh-ρ 𝒳)
≪ 𝒳 [-,-]≫ .coh-cmp (f₁ , g₁) (f₀ , g₀) {h} =
  cmp₁ 𝒳
    (cmp₀* 𝒳
      (cmp₁ 𝒳
        (coh-α 𝒳)
        (cmp₀* 𝒳
          (coh-α 𝒳)
          (idn₁ 𝒳)))
      (idn₁ 𝒳))
    (inv₁ 𝒳 (coh-α 𝒳))
