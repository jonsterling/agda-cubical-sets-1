module Basis.Category.Transform where

open import Basis.Category.Boot
open import Basis.Category.Functor

record Transform {𝒳 𝒴} (F G : Functor 𝒳 𝒴) : Set where
  no-eta-equality
  field
    ap₀ : ∀ x
      → 𝒴 ⊧ ap₀ F x ⇾ ap₀ G x
    ap₁ : ∀ {x y}
      → (f : 𝒳 ⊧ x ⇾ y)
      → 𝒴 ⊧ cmp₀ 𝒴 (ap₀ y) (ap₁ F f) ⇔ cmp₀ 𝒴 (ap₁ G f) (ap₀ x)
open Transform public
{-# DISPLAY Transform.ap₀ α x = α x #-}
{-# DISPLAY Transform.ap₁ α f = α f #-}
