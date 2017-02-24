module Basis.Setoid.Construction.Equalizer where

open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Map
open import Basis.Setoid.Map
open import Basis.Prelude

module Equalizer {𝒳 𝒴 : Setoid} (F G : Map 𝒳 𝒴) where
  Equalizer : Setoid
  Equalizer .obj = T.Σ (obj 𝒳) λ x → hom 𝒴 (ap₀ F x) (ap₀ G x)
  Equalizer .hom (x₀ ▸ f₀) (x₁ ▸ f₁) = hom 𝒳 x₀ x₁
  Equalizer .idn₀ = idn₀ 𝒳
  Equalizer .cmp₀ = cmp₀ 𝒳
  Equalizer .inv₀ = inv₀ 𝒳

  from : Map Equalizer 𝒳
  from .ap₀ = T.fst
  from .ap₁ = T.idn

  module _ {𝒵} (H : Map 𝒵 𝒳) (ψ : hom (≪Map≫ 𝒵 𝒴) (cmp F H) (cmp G H)) where
    into : Map 𝒵 Equalizer
    into .ap₀ z = ap₀ H z ▸ ψ {z}
    into .ap₁ f = ap₁ H f
open Equalizer public
  using (Equalizer)
