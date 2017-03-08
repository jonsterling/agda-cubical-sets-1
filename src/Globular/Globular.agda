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

≪Globular≫ : Category
≪Globular≫ = C.≪Presheaf≫ Globes

-- data List≈ {A : Set} (rel : A → A → Set) : List A → List A → Set where
--   [] : List≈ rel [] []
--   _∷_ : ∀ {x y xs ys} → rel x y → List≈ rel xs ys → List≈ rel (x ∷ xs) (y ∷ ys)

-- ≪List≫ : Setoid → Setoid
-- ≪List≫ A .S.obj = List  (A .S.obj)
-- ≪List≫ A .S.hom = List≈ (A .S.hom)
-- ≪List≫ A .idn₀ {[]} = []
-- ≪List≫ A .idn₀ {x ∷ xs} = A .idn₀ ∷ ≪List≫ A .S.idn₀
-- ≪List≫ A .cmp₀ [] p = p
-- ≪List≫ A .cmp₀ (g ∷ q) (f ∷ p) = A .cmp₀ g f ∷ ≪List≫ A .cmp₀ q p
-- ≪List≫ A .inv₀ [] = []
-- ≪List≫ A .inv₀ (f ∷ p) = A .inv₀ f ∷ ≪List≫ A .inv₀ p

-- ≪map≫ : {A B : Set} → (A → B) → (List A → List B)
-- ≪map≫ f [] = []
-- ≪map≫ f (x ∷ xs) = f x ∷ ≪map≫ f xs

-- {-# TERMINATING #-}
-- Unlabeled : Globular
-- Unlabeled .ap₀ zero = S.𝟙
-- Unlabeled .ap₀ (succ n) = ≪List≫ (Unlabeled .ap₀ n)
-- Unlabeled .ap₁ idn = S.idn
-- Unlabeled .ap₁ (cmp q p) = S.cmp (Unlabeled .ap₁ p) (Unlabeled .ap₁ q)
-- Unlabeled .ap₁ {y = zero}   dom .ap₀ xs = *
-- Unlabeled .ap₁ {y = succ n} dom .ap₀ xs = ≪map≫ (ap₀ (ap₁ Unlabeled {y = n} dom)) xs
-- Unlabeled .ap₁ {y = zero} dom .ap₁ p = *
-- Unlabeled .ap₁ {y = succ n} dom .ap₁ [] = []
-- Unlabeled .ap₁ {y = succ n} dom .ap₁ (f ∷ p) = ap₁ (ap₁ Unlabeled {y = n} dom) f ∷ ap₁ (ap₁ Unlabeled {y = succ n} dom) p
-- Unlabeled .ap₁ {y = zero}   cod .ap₀ xs = *
-- Unlabeled .ap₁ {y = succ n} cod .ap₀ xs = ≪map≫ (ap₀ (ap₁ Unlabeled {y = n} cod)) xs
-- Unlabeled .ap₁ {y = zero} cod .ap₁ p = *
-- Unlabeled .ap₁ {y = succ n} cod .ap₁ [] = []
-- Unlabeled .ap₁ {y = succ n} cod .ap₁ (f ∷ p) = ap₁ (ap₁ Unlabeled {y = n} cod) f ∷ ap₁ (ap₁ Unlabeled {y = succ n} cod) p
-- Unlabeled .ap₂ {y = n} idn = Unlabeled .ap₀ n .S.idn₀
-- Unlabeled .ap₂ {y = n} (cmp q p) = Unlabeled .ap₀ n .S.cmp₀ (Unlabeled .ap₂ q) (Unlabeled .ap₂ p)
-- Unlabeled .ap₂ {y = n} (inv p) = Unlabeled .ap₀ n .inv₀ (Unlabeled .ap₂ p)
-- Unlabeled .ap₂ {y = n} dom = {!!}
-- Unlabeled .ap₂ {y = n} cod = {!!}
-- Unlabeled .ap₂ {y = n} rel.coh-λ = Unlabeled .ap₀ n .S.idn₀
-- Unlabeled .ap₂ {y = n} rel.coh-ρ = Unlabeled .ap₀ n .S.idn₀
-- Unlabeled .ap₂ {y = n} rel.coh-α = Unlabeled .ap₀ n .S.idn₀
-- Unlabeled .ap₂ {y = n} (rel.coh-ω q p) = {!!}
-- Unlabeled .coh-idn {n} = Unlabeled .ap₀ n .S.idn₀
-- Unlabeled .coh-cmp {m}{n}{o} g f = Unlabeled .ap₀ o .S.idn₀
