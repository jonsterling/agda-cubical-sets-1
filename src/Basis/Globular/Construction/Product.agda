module Basis.Globular.Construction.Product where

open import Basis.Globular.Boot
open import Basis.Prelude

_⊗_ : Globular → Globular → Globular
(𝒳 ⊗ 𝒴) .● = ● 𝒳 T.⊗ ● 𝒴
(𝒳 ⊗ 𝒴) .∂ (x₀ , y₀) (x₁ , y₁) = ∂ 𝒳 x₀ x₁ ⊗ ∂ 𝒴 y₀ y₁
