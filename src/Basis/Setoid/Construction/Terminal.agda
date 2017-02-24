module Basis.Setoid.Construction.Terminal where

open import Basis.Setoid.Boot
open import Basis.Setoid.Map
open import Basis.Prelude

𝟙 : Setoid
𝟙 .obj = T.𝟙
𝟙 .hom * * = T.𝟙
𝟙 .idn₀ = *
𝟙 .cmp₀ * * = *
𝟙 .inv₀ * = *

! : ∀ {𝒳} → Map 𝒳 𝟙
! .ap₀ = T.!
! .ap₁ = T.!
