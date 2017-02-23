module Basis.Setoid.Map where

open import Basis.Setoid.Boot

record Map (𝒳 𝒴 : Setoid) : Set where
  no-eta-equality
  field
    ap₀ : obj 𝒳 → obj 𝒴
    ap₁ : ∀ {x y} → hom 𝒳 x y → hom 𝒴 (ap₀ x) (ap₀ y)
open Map public
{-# DISPLAY Map.ap₀ F x = F x #-}
{-# DISPLAY Map.ap₁ F f = F f #-}
