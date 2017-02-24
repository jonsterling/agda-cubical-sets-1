module Basis.Setoid.Construction.Initial where

open import Basis.Setoid.Boot
open import Basis.Setoid.Map
open import Basis.Prelude

𝟘 : Setoid
𝟘 .obj = T.𝟘
𝟘 .hom _ _ = T.𝟘
𝟘 .idn₀ {()}
𝟘 .cmp₀ () ()
𝟘 .inv₀ ()

¡ : ∀ {𝒳} → Map 𝟘 𝒳
¡ .ap₀ = T.¡
¡ .ap₁ = T.¡
