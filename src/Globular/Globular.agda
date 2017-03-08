module Globular.Globular where

open import Basis.Prelude

module 𝔾 where
  data hom : (m n : ℕ) → Set where
    idn : ∀ {m} → hom m m
    cmp : ∀ {m n o} (g : hom n o) (f : hom m n) → hom m o
    dom : ∀ {m} → hom m (succ m)
    cod : ∀ {m} → hom m (succ m)

  data rel : ∀ {m n} (f g : hom m n) → Set where
    idn : ∀ {m n f} → rel {m}{n} f f
    cmp : ∀ {m n f g h} (β : rel {m}{n} g h) (α : rel {m}{n} f g) → rel {m}{n} f h
    inv : ∀ {m n f g} (α : rel {m}{n} f g) → rel {m}{n} g f
    dom : ∀ {m} → rel {m}{succ (succ m)} (cmp dom dom) (cmp cod dom)
    cod : ∀ {m} → rel {m}{succ (succ m)} (cmp dom cod) (cmp cod cod)
    coh-λ : ∀ {m n f} → rel {m}{n} (cmp idn f) f
    coh-ρ : ∀ {m n f} → rel {m}{n} (cmp f idn) f
    coh-α : ∀ {m n o p f g h} → rel (cmp {m}{n}{p} (cmp {n}{o}{p} h g) f) (cmp {m}{o}{p} h (cmp {m}{n}{o} g f))
    coh-ω : ∀ {m n o f₀ f₁ g₀ g₁} (β : rel {n}{o} g₀ g₁) (α : rel {m}{n} f₀ f₁) → rel (cmp g₀ f₀) (cmp g₁ f₁)
open 𝔾
  hiding (coh-λ)
  hiding (coh-ρ)
  hiding (coh-α)
  hiding (coh-ω)

open import Basis

Globes : Category
⟪ Globes ⟫ .● = ℕ
⟪ Globes ⟫ .∂ x y .● = 𝔾.hom x y
⟪ Globes ⟫ .∂ x y .∂ f g .● = 𝔾.rel f g
⟪ Globes ⟫ .∂ x y .∂ f g .∂ _ _ = G.𝟘
Globes .idn₀ = 𝔾.idn
Globes .cmp₀ = 𝔾.cmp
Globes .idn₁ = 𝔾.idn
Globes .cmp₁ = 𝔾.cmp
Globes .inv₁ = 𝔾.inv
Globes .coh-λ = 𝔾.coh-λ
Globes .coh-ρ = 𝔾.coh-ρ
Globes .coh-α = 𝔾.coh-α
Globes .coh-ω = 𝔾.coh-ω

Globular : Set
Globular = C.Presheaf Globes
