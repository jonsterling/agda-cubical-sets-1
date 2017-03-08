module Basis.Graph.Construction.Product where

open import Basis.Graph.Boot
open import Basis.Prelude

_⊗_ : Graph → Graph → Graph
(𝒳 ⊗ 𝒴) .● = ● 𝒳 T.⊗ ● 𝒴
(𝒳 ⊗ 𝒴) .∂ (x₀ , y₀) (x₁ , y₁) = ∂ 𝒳 x₀ x₁ ⊗ ∂ 𝒴 y₀ y₁
