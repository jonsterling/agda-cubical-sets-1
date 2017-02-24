module Cubical.DeMorgan where

open import Basis
open import Cubical.Nominal

module 𝕀 where
  infix  0 _≅_
  infix  8 ¬_
  infixr 6 _∨_
  infixr 7 _∧_

  data DeMorgan (Γ : Symbols) : Set where
    var : (i : Name Γ) → DeMorgan Γ
    #0 : DeMorgan Γ
    #1 : DeMorgan Γ
    _∨_ : (a b : DeMorgan Γ) → DeMorgan Γ
    _∧_ : (a b : DeMorgan Γ) → DeMorgan Γ
    ¬_ : (a : DeMorgan Γ) → DeMorgan Γ

  instance
    ∈-stop : ∀ {Γ} (x : String) → x ∈ x ∷ Γ
    ∈-stop x = stop

    ∈-step : ∀ {y Γ} → (x : String) ⦃ ε : x ∈ Γ ⦄ ⦃ p : x ≢ y ⦄ → x ∈ y ∷ Γ
    ∈-step {y} x ⦃ ε ⦄ ⦃ p ⦄ = step y p ε

    ≪_≫ : ∀ {Γ} (x : String) ⦃ ε : x ∈ Γ ⦄ → DeMorgan Γ
    ≪ x ≫ ⦃ ε ⦄ = var (pt x ε)

  data _≅_ {Γ} : (a b : DeMorgan Γ) → Set where
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
open 𝕀 public
  hiding (module DeMorgan)
  hiding (module _≅_)
  hiding (_≅_)
  hiding (idn)
  hiding (cmp)
  hiding (inv)
