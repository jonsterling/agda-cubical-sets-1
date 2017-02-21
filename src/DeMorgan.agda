{-# OPTIONS --type-in-type #-}

module DeMorgan where

open import Category
open import Globular
open import Prelude
  hiding (¬_)
open import Setoid
  hiding (module Setoid)
  using (Setoid)
open import Symbol

infix  0 _≅_
infix  4 ¬_
infixr 2 _∨_
infixr 3 _∧_

data 𝕀 (Γ : Symbols) : Set where
  var : (i : Name Γ) → 𝕀 Γ
  #0 : 𝕀 Γ
  #1 : 𝕀 Γ
  _∨_ : (a b : 𝕀 Γ) → 𝕀 Γ
  _∧_ : (a b : 𝕀 Γ) → 𝕀 Γ
  ¬_ : (a : 𝕀 Γ) → 𝕀 Γ

instance
  ∈-stop : ∀ {Γ} (x : String) → x ∈ x ∷ Γ
  ∈-stop x = stop

  ∈-step : ∀ {y Γ} → (x : String) ⦃ ε : x ∈ Γ ⦄ ⦃ p : x ≢ y ⦄ → x ∈ y ∷ Γ
  ∈-step {y} x ⦃ ε ⦄ ⦃ p ⦄ = step y p ε

  ≪_≫ : ∀ {Γ} (x : String) ⦃ ε : x ∈ Γ ⦄ → 𝕀 Γ
  ≪ x ≫ ⦃ ε ⦄ = var (pt x ε)

data _≅_ {Γ} : (a b : 𝕀 Γ) → Set where
  idn -- identity
    : ∀ {a b}
    → a ≡ b
    → a ≅ b
  cmp
    : ∀ {a b c}
    → (q : b ≅ c)
    → (p : a ≅ b)
    → a ≅ c
  inv -- symmetry
    : ∀ {a b}
    → (p : a ≅ b)
    → b ≅ a
  ∨-abs -- absorption
    : ∀ {a b}
    → a ∨ a ∧ b ≅ a
  ∨-ass -- associativity
    : ∀ {a b c}
    → a ∨ (b ∨ c) ≅ (a ∨ b) ∨ c
  ∨-com -- commutativity
    : ∀ {a b}
    → a ∨ b ≅ b ∨ a
  ∨-dis -- distributivity
    : ∀ {a b c}
    → a ∨ b ∧ c ≅ (a ∨ b) ∧ (a ∨ c)
  ∨-ide -- idempotency
    : ∀ {a}
    → a ∨ a ≅ a
  ∨-rsp -- congruence
    : ∀ {a₀ a₁ b₀ b₁}
    → a₀ ≅ a₁
    → b₀ ≅ b₁
    → a₀ ∨ b₀ ≅ a₁ ∨ b₁
  ∨-uni
    : ∀ {a}
    → a ∨ #0 ≅ a
  ∧-abs
    : ∀ {a b}
    → a ∧ (a ∨ b) ≅ a
  ∧-ass
    : ∀ {a b c}
    → a ∧ (b ∧ c) ≅ (a ∧ b) ∧ c
  ∧-com
    : ∀ {a b}
    → a ∧ b ≅ b ∧ a
  ∧-dis
    : ∀ {a b c}
    → a ∧ (b ∨ c) ≅ a ∧ b ∨ a ∧ c
  ∧-ide
    : ∀ {a}
    → a ∧ a ≅ a
  ∧-rsp
    : ∀ {a₀ a₁ b₀ b₁}
    → a₀ ≅ a₁
    → b₀ ≅ b₁
    → a₀ ∧ b₀ ≅ a₁ ∧ b₁
  ∧-uni
    : ∀ {a}
    → a ∧ #1 ≅ a
  ¬-dis-∧
    : ∀ {a b}
    → ¬ (a ∧ b) ≅ ¬ a ∨ ¬ b
  ¬-dis-∨
    : ∀ {a b}
    → ¬ (a ∨ b) ≅ ¬ a ∧ ¬ b
  ¬-inv
    : ∀ {a}
    → ¬ ¬ a ≅ a
  ¬-rsp
    : ∀ {a₀ a₁}
    → a₀ ≅ a₁
    → ¬ a₀ ≅ ¬ a₁
  ¬-#0
    : ¬ #0 ≅ #1
  ¬-#1
    : ¬ #1 ≅ #0

postulate
  distinct : ∀ {Γ} → T.¬ _≅_ {Γ} #0 #1
