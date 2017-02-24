module Basis.Setoid.Construction.Coequalizer where

open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Map
open import Basis.Setoid.Map
open import Basis.Prelude

module Coequalizer {𝒳 𝒴 : Setoid} (F G : Map 𝒳 𝒴) where
  data ⊢hom (y₀ y₁ : obj 𝒴) : Set where
    ⊢rel
      : ∀ x
      → (p₀ : hom 𝒴 y₀ (ap₀ F x))
      → (p₁ : hom 𝒴 y₁ (ap₀ G x))
      → ⊢hom y₀ y₁
    ⊢idn
      : (p : hom 𝒴 y₀ y₁)
      → ⊢hom y₀ y₁
    ⊢cmp
      : ∀ {y}
      → (q : ⊢hom y y₁)
      → (p : ⊢hom y₀ y)
      → ⊢hom y₀ y₁
    ⊢inv
      : (p : ⊢hom y₁ y₀)
      → ⊢hom y₀ y₁

  Coequalizer : Setoid
  Coequalizer .obj = obj 𝒴
  Coequalizer .hom = ⊢hom
  Coequalizer .idn₀ = ⊢idn (idn₀ 𝒴)
  Coequalizer .cmp₀ = ⊢cmp
  Coequalizer .inv₀ = ⊢inv

  into : Map 𝒴 Coequalizer
  into .ap₀ = T.idn
  into .ap₁ = ⊢idn

  module _ {𝒵} (H : Map 𝒴 𝒵) (ψ : hom (≪Map≫ 𝒳 𝒵) (cmp H F) (cmp H G)) where
    ⊢ap₁ : ∀ {y₀ y₁} → ⊢hom y₀ y₁ → hom 𝒵 (ap₀ H y₀) (ap₀ H y₁)
    ⊢ap₁ (⊢rel x p₀ p₁) = cmp₀ 𝒵 (cmp₀ 𝒵 (ap₁ H (inv₀ 𝒴 p₁)) (ψ {x})) (ap₁ H p₀)
    ⊢ap₁ (⊢idn p) = ap₁ H p
    ⊢ap₁ (⊢cmp q p) = cmp₀ 𝒵 (⊢ap₁ q) (⊢ap₁ p)
    ⊢ap₁ (⊢inv p) = inv₀ 𝒵 (⊢ap₁ p)

    from : Map Coequalizer 𝒵
    from .ap₀ = ap₀ H
    from .ap₁ = ⊢ap₁
open Coequalizer public
  using (Coequalizer)
