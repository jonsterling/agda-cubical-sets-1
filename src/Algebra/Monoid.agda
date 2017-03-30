module Algebra.Monoid where

open import Basis.Prelude
open import Basis.Setoid
open import Basis.Category
open import Basis.Graph

record Semigroup : Set where
  no-eta-equality
  field
    car : Setoid
    mul : S.Map (car S.⊗ car) car
  field
    coh-α
      : ∀ x y z
      → hom car (ap₀ mul ((ap₀ mul (x , y)) , z)) (ap₀ mul (x , (ap₀ mul (y , z))))

record Monoid : Set where
  no-eta-equality
  field
    car : Setoid
    idn : obj car
    mul : S.Map (car S.⊗ car) car
  field
    coh-λ
      : ∀ x
      → hom car (ap₀ mul (idn , x)) x
    coh-ρ
      : ∀ x
      → hom car (ap₀ mul (x , idn)) x
    coh-α
      : ∀ x y z
      → hom car (ap₀ mul ((ap₀ mul (x , y)) , z)) (ap₀ mul (x , (ap₀ mul (y , z))))

open Monoid public
open Semigroup public

Monoid⇒Semigroup : Monoid → Semigroup
Monoid⇒Semigroup M .car = M .car
Monoid⇒Semigroup M .mul = M .mul
Monoid⇒Semigroup M .coh-α = M .coh-α

≪Semigroup≫ : Category
⟪ ≪Semigroup≫ ⟫ .● = Semigroup
⟪ ≪Semigroup≫ ⟫ .∂ S T = {!!}
idn₀ ≪Semigroup≫ = {!!}
cmp₀ ≪Semigroup≫ = {!!}
idn₁ ≪Semigroup≫ = {!!}
cmp₁ ≪Semigroup≫ = {!!}
inv₁ ≪Semigroup≫ = {!!}
coh-λ ≪Semigroup≫ = {!!}
coh-ρ ≪Semigroup≫ = {!!}
coh-α ≪Semigroup≫ = {!!}
coh-ω ≪Semigroup≫ = {!!}
