module Basis.Prelude.Path where

open import Basis.Prelude.Void

module ≡ where
  open import Agda.Builtin.Equality public

  infix 4 _≢_

  _≢_ : ∀ {a} {A : Set a} (x : A) → A → Set a
  x ≢ y = ¬ (x ≡ y)

  idn : {A : Set} {a : A} → a ≡ a
  idn = refl

  cmp : {A : Set} {a b c : A} → b ≡ c → a ≡ b → a ≡ c
  cmp refl q = q

  seq : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  seq p refl = p

  inv : {A : Set} {a b : A} → a ≡ b → b ≡ a
  inv refl = refl

  subst : ∀ {A : Set} {x y} (Ψ : A → Set) (ρ : x ≡ y) → Ψ x → Ψ y
  subst Ψ refl x = x

  ap : ∀ {A B : Set} {x₀ x₁} (f : A → B) → x₀ ≡ x₁ → f x₀ ≡ f x₁
  ap f refl = refl

  ap² : ∀ {A B C : Set} {x₀ x₁ y₀ y₁} (f : A → B → C) → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
  ap² f refl refl = refl
open ≡ public
  using (_≡_)
  using (refl)
