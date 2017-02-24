module Basis.Setoid.Construction.Coequalizer where

open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Free
open import Basis.Setoid.Construction.Map
open import Basis.Setoid.Map
open import Basis.Prelude

module Coequalizer {𝒳 𝒴 : Setoid} (F G : Map 𝒳 𝒴) where
  data Quotient (y₀ y₁ : obj 𝒴) : Set where
    ρ : ∀ x (p₀ : hom 𝒴 y₀ (ap₀ F x)) (p₁ : hom 𝒴 y₁ (ap₀ G x)) → Quotient y₀ y₁
    ι : (p : hom 𝒴 y₀ y₁) → Quotient y₀ y₁

  Coequalizer : Setoid
  Coequalizer = Free Quotient

  into : Map 𝒴 Coequalizer
  into .ap₀ y = y
  into .ap₁ g = Free.≪ ι g ≫

  module _ {𝒵} (H : Map 𝒴 𝒵) (ψ : hom (≪Map≫ 𝒳 𝒵) (cmp H F) (cmp H G)) where
    ⊢ap₁ : ∀ {y₀ y₁} → hom Coequalizer y₀ y₁ → hom 𝒵 (ap₀ H y₀) (ap₀ H y₁)
    ⊢ap₁ ≪ ρ x p₀ p₁ ≫ = cmp₀ 𝒵 (cmp₀ 𝒵 (ap₁ H (inv₀ 𝒴 p₁)) (ψ {x})) (ap₁ H p₀)
    ⊢ap₁ ≪ ι p ≫ = ap₁ H p
    ⊢ap₁ ▸idn = idn₀ 𝒵
    ⊢ap₁ (▸cmp q p) = cmp₀ 𝒵 (⊢ap₁ q) (⊢ap₁ p)
    ⊢ap₁ (▸inv p) = inv₀ 𝒵 (⊢ap₁ p)

    from : Map Coequalizer 𝒵
    from .ap₀ = ap₀ H
    from .ap₁ = ⊢ap₁
open Coequalizer public
  using (Coequalizer)
