module Algebra.Monoid where

open import Basis.Prelude
open import Basis.Setoid
open import Basis.Category
open import Basis.Graph

_⊧_≐_ : (S : Setoid) → S .obj → S .obj → Set
_⊧_≐_ = Setoid.hom

{-# DISPLAY Setoid.hom = _⊧_≐_ #-}

record Semigroup : Set where
  no-eta-equality
  field
    car : Setoid
    mul : S.Map (car S.⊗ car) car

  private
    _·_ : car .obj → car .obj → car .obj
    _·_ m n = ap₀ mul (m , n)

  field
    coh-α
      : ∀ x y z
      → car ⊧ (x · y) · z ≐ (x · (y · z))

record Semigroup/Hom (S T : Semigroup) : Set where
  open Semigroup
  field
    ap : S.Map (S .car) (T .car)
    mul : ∀ {m n} → T .car ⊧ ap₀ ap (ap₀ (S .mul) (m , n)) ≐ ap₀ (T .mul) ((ap₀ ap m) , (ap₀ ap n))

record Monoid : Set where
  no-eta-equality
  field
    car : Setoid
    idn : obj car
    mul : S.Map (car S.⊗ car) car

  private
    _·_ : car .obj → car .obj → car .obj
    _·_ m n = ap₀ mul (m , n)

  field
    coh-λ
      : ∀ x
      → car ⊧ idn · x ≐ x
    coh-ρ
      : ∀ x
      → car ⊧ x · idn ≐ x
    coh-α
      : ∀ x y z
      → car ⊧ (x · y) · z ≐ (x · (y · z))

open Semigroup public
open Semigroup/Hom public
open Monoid public

Monoid⇒Semigroup : Monoid → Semigroup
Monoid⇒Semigroup M .car = M .car
Monoid⇒Semigroup M .mul = M .mul
Monoid⇒Semigroup M .coh-α = M .coh-α

≪Semigroup≫ : Category
⟪ ≪Semigroup≫ ⟫ .● = Semigroup
⟪ ≪Semigroup≫ ⟫ .∂ S T .● = Semigroup/Hom S T
⟪ ≪Semigroup≫ ⟫ .∂ S T .∂ F G .● = S.≪Map≫ (S .car) (T .car) ⊧ F .ap ≐ G .ap
⟪ ≪Semigroup≫ ⟫ .∂ S T .∂ F G .∂ α β = G.𝟘
≪Semigroup≫ .idn₀ {S} .ap = C.≪Setoid≫ .idn₀
≪Semigroup≫ .idn₀ {S} .mul = S .car .idn₀
cmp₀ ≪Semigroup≫ F G .ap = C.≪Setoid≫ .cmp₀ (F .ap) (G .ap)
cmp₀ ≪Semigroup≫ {S} {T} {U} F G .mul = U .car .cmp₀ (F .mul) (F .ap .ap₁ (G .mul))
idn₁ ≪Semigroup≫ {S} {T} {F} = C.≪Setoid≫ .idn₁ {S .car} {T .car} {F .ap}
cmp₁ ≪Semigroup≫ {S} {T} {F} {G} {H} = C.≪Setoid≫ .cmp₁ {S .car} {T .car} {F .ap} {G .ap} {H .ap}
inv₁ ≪Semigroup≫ {S} {T} {F} {G} = C.≪Setoid≫ .inv₁ {S .car} {T .car} {F .ap} {G .ap}
coh-λ ≪Semigroup≫ {S} {T} = T .car .idn₀
coh-ρ ≪Semigroup≫ {S} {T} = T .car .idn₀
coh-α ≪Semigroup≫ {S} {T} {U} {V} = V .car .idn₀
coh-ω ≪Semigroup≫ {S} {T} {U} {F} {G} {H} {I} α β = C.≪Setoid≫ .coh-ω {S .car} {T .car} {U .car} {F .ap} {G .ap} {H .ap} {I .ap} α β

