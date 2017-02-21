{-# OPTIONS --type-in-type #-}

module CubicalSet.Presheaf where

open import Category
open import Cube
  hiding (idn)
open import DeMorgan as 𝕀
  hiding (idn)
  hiding (cmp)
  hiding (inv)
open import Globular
open import Prelude
  hiding (¬_)
open import Setoid
  hiding (module Setoid)
open import Symbol

□Set : Set
□Set = Presheaf Cube.cat

≪□Set≫ : Category
≪□Set≫ = ≪Presheaf≫ Cube.cat

-- the formal or representable cube
□ : Symbols → □Set
□ = ap₀ (Yoneda Cube.cat)

data Interval (I : Symbols) : Set where
  west : Interval I
  east : Interval I
  walk : (φ : 𝕀 I) → Interval I

interval : □Set
interval .ap₀ I .obj = Interval I
interval .ap₀ I .hom east east = T.𝟙
interval .ap₀ I .hom east (walk φ₁) = #1 𝕀.≅ φ₁
interval .ap₀ I .hom (walk φ₀) east = φ₀ 𝕀.≅ #1
interval .ap₀ I .hom (walk φ₀) (walk φ₁) = φ₀ 𝕀.≅ φ₁
interval .ap₀ I .hom (walk φ₀) west = φ₀ 𝕀.≅ #0
interval .ap₀ I .hom west (walk φ₁) = #0 𝕀.≅ φ₁
interval .ap₀ I .hom west west = T.𝟙
interval .ap₀ I .hom _ _ = T.𝟘
interval .ap₀ I .idn {west} = *
interval .ap₀ I .idn {east} = *
interval .ap₀ I .idn {walk φ} = 𝕀.idn refl
interval .ap₀ I .cmp {west} {west} {west} * * = *
interval .ap₀ I .cmp {west} {west} {east} () *
interval .ap₀ I .cmp {west} {west} {walk φ₂} q * = q
interval .ap₀ I .cmp {west} {east} {west} () ()
interval .ap₀ I .cmp {west} {east} {east} * ()
interval .ap₀ I .cmp {west} {east} {walk φ₂} q ()
interval .ap₀ I .cmp {west} {walk φ₁} {west} q p = *
interval .ap₀ I .cmp {west} {walk φ₁} {east} q p = 𝕀.distinct (𝕀.cmp q p)
interval .ap₀ I .cmp {west} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
interval .ap₀ I .cmp {east} {west} {west} * ()
interval .ap₀ I .cmp {east} {west} {east} () ()
interval .ap₀ I .cmp {east} {west} {walk φ₂} q ()
interval .ap₀ I .cmp {east} {east} {west} () *
interval .ap₀ I .cmp {east} {east} {east} * * = *
interval .ap₀ I .cmp {east} {east} {walk φ₂} q * = q
interval .ap₀ I .cmp {east} {walk φ₁} {west} q p = 𝕀.distinct (𝕀.cmp (𝕀.inv p) (𝕀.inv q))
interval .ap₀ I .cmp {east} {walk φ₁} {east} q p = *
interval .ap₀ I .cmp {east} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
interval .ap₀ I .cmp {walk φ₀} {west} {west} * p = p
interval .ap₀ I .cmp {walk φ₀} {west} {east} () p
interval .ap₀ I .cmp {walk φ₀} {west} {walk φ₂} q p = 𝕀.cmp q p
interval .ap₀ I .cmp {walk φ₀} {east} {west} () p
interval .ap₀ I .cmp {walk φ₀} {east} {east} * p = p
interval .ap₀ I .cmp {walk φ₀} {east} {walk φ₂} q p = 𝕀.cmp q p
interval .ap₀ I .cmp {walk φ₀} {walk φ₁} {west} q p = 𝕀.cmp q p
interval .ap₀ I .cmp {walk φ₀} {walk φ₁} {east} q p = 𝕀.cmp q p
interval .ap₀ I .cmp {walk φ₀} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
interval .ap₀ I .inv {west} {west} * = *
interval .ap₀ I .inv {west} {east} ()
interval .ap₀ I .inv {west} {walk φ₁} p = 𝕀.inv p
interval .ap₀ I .inv {east} {west} ()
interval .ap₀ I .inv {east} {east} * = *
interval .ap₀ I .inv {east} {walk φ₁} p = 𝕀.inv p
interval .ap₀ I .inv {walk φ₀} {west} p = 𝕀.inv p
interval .ap₀ I .inv {walk φ₀} {east} p = 𝕀.inv p
interval .ap₀ I .inv {walk φ₀} {walk φ₁} p = 𝕀.inv p
interval .ap₁ f .ap₀ west = west
interval .ap₁ f .ap₀ east = east
interval .ap₁ f .ap₀ (walk φ) = walk (φ ≫= f)
interval .ap₁ f .ap₁ {west} {west} * = *
interval .ap₁ f .ap₁ {west} {east} ()
interval .ap₁ f .ap₁ {west} {walk φ₁} p = Cube.rsp-lhs f p
interval .ap₁ f .ap₁ {east} {west} ()
interval .ap₁ f .ap₁ {east} {east} * = *
interval .ap₁ f .ap₁ {east} {walk φ₁} p = Cube.rsp-lhs f p
interval .ap₁ f .ap₁ {walk φ₀} {west} p = Cube.rsp-lhs f p
interval .ap₁ f .ap₁ {walk φ₀} {east} p = Cube.rsp-lhs f p
interval .ap₁ f .ap₁ {walk φ₀} {walk φ₁} p = Cube.rsp-lhs f p
interval .ap₂ α {west} = *
interval .ap₂ α {east} = *
interval .ap₂ {Γ}{Δ}{f}{g} α {walk φ} = Cube.rsp-rhs φ f g α
interval .coh-idn {Γ} {west} = *
interval .coh-idn {Γ} {east} = *
interval .coh-idn {Γ} {walk φ} = 𝕀.idn Cube.idn
interval .coh-cmp {x₁} {y} {z} g f {west} = *
interval .coh-cmp {x₁} {y} {z} g f {east} = *
interval .coh-cmp {x₁} {y} {z} g f {walk φ} = 𝕀.idn (Cube.ass φ f g)
