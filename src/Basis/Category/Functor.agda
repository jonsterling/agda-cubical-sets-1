module Basis.Category.Functor where

open import Basis.Category.Boot
open import Basis.Globular

record Functor (𝒳 𝒴 : Category) : Set where
  no-eta-equality
  field
    ap₀ : ● ⟪ 𝒳 ⟫ → ● ⟪ 𝒴 ⟫
    ap₁ : ∀ {x y} → 𝒳 ⊧ x ⇾ y → 𝒴 ⊧ ap₀ x ⇾ ap₀ y
    ap₂ : ∀ {x y} {f g : 𝒳 ⊧ x ⇾ y} → 𝒳 ⊧ f ⇔ g → 𝒴 ⊧ ap₁ f ⇔ ap₁ g
  field
    coh-idn
      : ∀ {x}
      → 𝒴 ⊧ ap₁ (idn₀ 𝒳 {x}) ⇔ idn₀ 𝒴 {ap₀ x}
    coh-cmp
      : ∀ {x y z}
      → (g : 𝒳 ⊧ y ⇾ z) (f : 𝒳 ⊧ x ⇾ y)
      → 𝒴 ⊧ ap₁ (cmp₀ 𝒳 g f) ⇔ cmp₀ 𝒴 (ap₁ g) (ap₁ f)
open Functor public
{-# DISPLAY Functor.ap₀ F x = F x #-}
{-# DISPLAY Functor.ap₁ F f = F f #-}
{-# DISPLAY Functor.ap₂ F α = F α #-}
