module Basis.Category.Boot where

open import Basis.Graph
open import Basis.Prelude
open import Basis.Syntax public

record Category : Set where
  no-eta-equality
  field ⟪_⟫ : Graph
  open G.Cell.Syntax {⟪_⟫}
  field
    idn₀ : ∀ {x}
      → x ⇾ x
    cmp₀ : ∀ {x y z}
      → (g : y ⇾ z) (f : x ⇾ y)
      → x ⇾ z
    idn₁ : ∀ {x y} {f : x ⇾ y}
      → f ⇔ f
    cmp₁ : ∀ {x y} {f g h : x ⇾ y}
      → (β : g ⇔ h) (α : f ⇔ g)
      → f ⇔ h
    inv₁ : ∀ {x y} {f g : x ⇾ y}
      → (α : f ⇔ g)
      → g ⇔ f
    coh-λ : ∀ {x y} {f : x ⇾ y}
      → cmp₀ idn₀ f ⇔ f
    coh-ρ : ∀ {x y} {f : x ⇾ y}
      → cmp₀ f idn₀ ⇔ f
    coh-α : ∀ {w x y z} {f : w ⇾ x} {g : x ⇾ y} {h : y ⇾ z}
      → cmp₀ (cmp₀ h g) f ⇔ cmp₀ h (cmp₀ g f)
    coh-ω : ∀ {x y z} {f₀ f₁ : x ⇾ y} {g₀ g₁ : y ⇾ z}
      → (β : g₀ ⇔ g₁) (α : f₀ ⇔ f₁)
      → cmp₀ g₀ f₀ ⇔ cmp₀ g₁ f₁
  coh-ω-λ : ∀ {x y z} {f : x ⇾ y} {g₀ g₁ : y ⇾ z}
    → (β : g₀ ⇔ g₁)
    → cmp₀ g₀ f ⇔ cmp₀ g₁ f
  coh-ω-λ β = coh-ω β idn₁
  coh-ω-ρ : ∀ {x y z} {f₀ f₁ : x ⇾ y} {g : y ⇾ z}
    → (α : f₀ ⇔ f₁)
    → cmp₀ g f₀ ⇔ cmp₀ g f₁
  coh-ω-ρ α = coh-ω idn₁ α
  infix 0 _⊧_⇾_
  infix 0 _⊧_⇔_
  _⊧_⇾_ = G.cell ⟪_⟫ 1
  _⊧_⇔_ = G.cell ⟪_⟫ 2
open Category public
{-# DISPLAY Category.idn₀ A = ↻ #-}
{-# DISPLAY Category.cmp₀ A g f = g ∘ f #-}
open G.Cell.Syntax public
