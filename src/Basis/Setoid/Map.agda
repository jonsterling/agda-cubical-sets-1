module Basis.Setoid.Map where

open import Basis.Prelude
open import Basis.Setoid.Boot

record Map (𝒳 𝒴 : Setoid) : Set where
  no-eta-equality
  field
    ap₀ : obj 𝒳 → obj 𝒴
    ap₁ : ∀ {x y} → hom 𝒳 x y → hom 𝒴 (ap₀ x) (ap₀ y)
open Map public
{-# DISPLAY Map.ap₀ F x = F x #-}
{-# DISPLAY Map.ap₁ F f = F f #-}

idn : ∀ {𝒳} → Map 𝒳 𝒳
idn .ap₀ = T.idn
idn .ap₁ = T.idn

cmp : ∀ {𝒳 𝒴 𝒵} → Map 𝒴 𝒵 → Map 𝒳 𝒴 → Map 𝒳 𝒵
cmp G F .ap₀ = T.cmp (ap₀ G) (ap₀ F)
cmp G F .ap₁ = T.cmp (ap₁ G) (ap₁ F)
