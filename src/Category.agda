module Category where

open import Globular
open import Prelude

record Category : Set where
  no-eta-equality
  field quiver : Globular
  open CellSyntax {quiver}
  field
    idn₀ : ∀ {a}
      → a ⇾ a
    seq₀ : ∀ {a b c}
      → (f : a ⇾ b) (g : b ⇾ c)
      → a ⇾ c
    idn₁ : ∀ {a b} {f : a ⇾ b}
      → f ⇔ f
    seq₁ : ∀ {a b} {f g h : a ⇾ b}
      → (α : f ⇔ g)
      → (β : g ⇔ h)
      → f ⇔ h
    inv₁ : ∀ {a b} {f g : a ⇾ b}
      → (α : f ⇔ g)
      → g ⇔ f
    seq₀* : ∀ {a b c} {f₀ f₁ : a ⇾ b} {g₀ g₁ : b ⇾ c}
      → (α : f₀ ⇔ f₁)
      → (β : g₀ ⇔ g₁)
      → seq₀ f₀ g₀ ⇔ seq₀ f₁ g₁
    coh-λ : ∀ {a b} {f : a ⇾ b}
      → seq₀ idn₀ f ⇔ f
    coh-ρ : ∀ {a b} {f : a ⇾ b}
      → seq₀ f idn₀ ⇔ f
    coh-α : ∀ {a b c d} {f : a ⇾ b} {g : b ⇾ c} {h : c ⇾ d}
      → seq₀ f (seq₀ g h) ⇔ seq₀ (seq₀ f g) h
open Category public
open CellSyntax public

Void : Globular
● Void = T.𝟘
∂ Void () ()
