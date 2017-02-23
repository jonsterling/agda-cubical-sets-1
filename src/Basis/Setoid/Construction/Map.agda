module Basis.Setoid.Construction.Map where

open import Basis.Setoid.Boot
open import Basis.Setoid.Map

≪Map≫ : Setoid → Setoid → Setoid
≪Map≫ 𝒳 𝒴 .obj = Map 𝒳 𝒴
≪Map≫ 𝒳 𝒴 .hom F G = ∀ {x} → hom 𝒴 (ap₀ F x) (ap₀ G x)
≪Map≫ 𝒳 𝒴 .idn = idn 𝒴
≪Map≫ 𝒳 𝒴 .cmp β α {x} = cmp 𝒴 (β {x}) (α {x})
≪Map≫ 𝒳 𝒴 .inv α {x} = inv 𝒴 (α {x})
