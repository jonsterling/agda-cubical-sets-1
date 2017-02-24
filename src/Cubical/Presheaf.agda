module Cubical.Presheaf where

open import Basis
open import Cubical.DeMorgan
open import Cubical.Nominal
open import Cubical.Substitution

module Presheaf where
  □Set : Set
  □Set = C.Presheaf Sub.cat

  ≪□Set≫ : Category
  ≪□Set≫ = C.≪Presheaf≫ Sub.cat

  -- the formal or representable cube
  □ : Functor Sub.cat ≪□Set≫
  □ = C.Yoneda Sub.cat

  data Interval (I : Symbols) : Set where
    west : Interval I
    east : Interval I
    walk : (φ : DeMorgan I) → Interval I

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
  interval .ap₀ I .idn₀ {west} = *
  interval .ap₀ I .idn₀ {east} = *
  interval .ap₀ I .idn₀ {walk φ} = 𝕀.idn refl
  interval .ap₀ I .cmp₀ {west} {west} {west} * * = *
  interval .ap₀ I .cmp₀ {west} {west} {east} () *
  interval .ap₀ I .cmp₀ {west} {west} {walk φ₂} q * = q
  interval .ap₀ I .cmp₀ {west} {east} {west} () ()
  interval .ap₀ I .cmp₀ {west} {east} {east} * ()
  interval .ap₀ I .cmp₀ {west} {east} {walk φ₂} q ()
  interval .ap₀ I .cmp₀ {west} {walk φ₁} {west} q p = *
  interval .ap₀ I .cmp₀ {west} {walk φ₁} {east} q p = 𝕀.distinct (𝕀.cmp q p)
  interval .ap₀ I .cmp₀ {west} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp₀ {east} {west} {west} * ()
  interval .ap₀ I .cmp₀ {east} {west} {east} () ()
  interval .ap₀ I .cmp₀ {east} {west} {walk φ₂} q ()
  interval .ap₀ I .cmp₀ {east} {east} {west} () *
  interval .ap₀ I .cmp₀ {east} {east} {east} * * = *
  interval .ap₀ I .cmp₀ {east} {east} {walk φ₂} q * = q
  interval .ap₀ I .cmp₀ {east} {walk φ₁} {west} q p = 𝕀.distinct (𝕀.cmp (𝕀.inv p) (𝕀.inv q))
  interval .ap₀ I .cmp₀ {east} {walk φ₁} {east} q p = *
  interval .ap₀ I .cmp₀ {east} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp₀ {walk φ₀} {west} {west} * p = p
  interval .ap₀ I .cmp₀ {walk φ₀} {west} {east} () p
  interval .ap₀ I .cmp₀ {walk φ₀} {west} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp₀ {walk φ₀} {east} {west} () p
  interval .ap₀ I .cmp₀ {walk φ₀} {east} {east} * p = p
  interval .ap₀ I .cmp₀ {walk φ₀} {east} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp₀ {walk φ₀} {walk φ₁} {west} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp₀ {walk φ₀} {walk φ₁} {east} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp₀ {walk φ₀} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .inv₀ {west} {west} * = *
  interval .ap₀ I .inv₀ {west} {east} ()
  interval .ap₀ I .inv₀ {west} {walk φ₁} p = 𝕀.inv p
  interval .ap₀ I .inv₀ {east} {west} ()
  interval .ap₀ I .inv₀ {east} {east} * = *
  interval .ap₀ I .inv₀ {east} {walk φ₁} p = 𝕀.inv p
  interval .ap₀ I .inv₀ {walk φ₀} {west} p = 𝕀.inv p
  interval .ap₀ I .inv₀ {walk φ₀} {east} p = 𝕀.inv p
  interval .ap₀ I .inv₀ {walk φ₀} {walk φ₁} p = 𝕀.inv p
  interval .ap₁ f .ap₀ west = west
  interval .ap₁ f .ap₀ east = east
  interval .ap₁ f .ap₀ (walk φ) = walk (φ ≫= f)
  interval .ap₁ f .ap₁ {west} {west} * = *
  interval .ap₁ f .ap₁ {west} {east} ()
  interval .ap₁ f .ap₁ {west} {walk φ₁} p = Sub.⊢coh-ω-λ p
  interval .ap₁ f .ap₁ {east} {west} ()
  interval .ap₁ f .ap₁ {east} {east} * = *
  interval .ap₁ f .ap₁ {east} {walk φ₁} p = Sub.⊢coh-ω-λ p
  interval .ap₁ f .ap₁ {walk φ₀} {west} p = Sub.⊢coh-ω-λ p
  interval .ap₁ f .ap₁ {walk φ₀} {east} p = Sub.⊢coh-ω-λ p
  interval .ap₁ f .ap₁ {walk φ₀} {walk φ₁} p = Sub.⊢coh-ω-λ p
  interval .ap₂ α {west} = *
  interval .ap₂ α {east} = *
  interval .ap₂ {Γ}{Δ}{f}{g} α {walk φ} = Sub.⊢coh-ω-ρ φ α
  interval .coh-idn {Γ} {west} = *
  interval .coh-idn {Γ} {east} = *
  interval .coh-idn {Γ} {walk φ} = Sub.⊢coh-ρ
  interval .coh-cmp {x₁} {y} {z} g f {west} = *
  interval .coh-cmp {x₁} {y} {z} g f {east} = *
  interval .coh-cmp {x₁} {y} {z} g f {walk φ} = Sub.⊢coh-α φ
