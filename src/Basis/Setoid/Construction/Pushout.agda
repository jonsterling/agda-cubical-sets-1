module Basis.Setoid.Construction.Pushout where

open import Basis.Setoid.Boot
open import Basis.Setoid.Construction.Coequalizer
open import Basis.Setoid.Construction.Coproduct
open import Basis.Setoid.Map
open import Basis.Prelude

module Pushout where
  Pushout
    : ∀ {𝒳 𝒴 𝒵}
    → (F : Map 𝒵 𝒳)
    → (G : Map 𝒵 𝒴)
    → Setoid
  Pushout F G = Coequalizer (cmp inl F) (cmp inr G)

  into
    : ∀ {𝒳 𝒴 𝒵}
    → (F : Map 𝒵 𝒳)
    → (G : Map 𝒵 𝒴)
    → Map (𝒳 ⊕ 𝒴) (Pushout F G)
  into F G = Coequalizer.into (cmp inl F) (cmp inr G)
open Pushout public
  using (Pushout)
