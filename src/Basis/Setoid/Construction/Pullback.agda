module Basis.Setoid.Construction.Pullback where

open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Equalizer
open import Basis.Setoid.Construction.Product
open import Basis.Setoid.Map
open import Basis.Prelude

module Pullback where
  Pullback
    : ∀ {𝒳 𝒴 𝒵}
    → (F : Map 𝒳 𝒵)
    → (G : Map 𝒴 𝒵)
    → Setoid
  Pullback F G = Equalizer (cmp F fst) (cmp G snd)

  from
    : ∀ {𝒳 𝒴 𝒵}
    → (F : Map 𝒳 𝒵)
    → (G : Map 𝒴 𝒵)
    → Map (Pullback F G) (𝒳 ⊗ 𝒴)
  from F G = Equalizer.from (cmp F fst) (cmp G snd)
open Pullback public
  using (Pullback)
