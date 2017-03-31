module Algebra.Semigroup where

open import Basis.Prelude
open import Basis.Setoid
open import Basis.Category
open import Basis.Graph

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

open Semigroup public
open Semigroup/Hom public

≪Semigroup≫ : Category
⟪ ≪Semigroup≫ ⟫ .● = Semigroup
⟪ ≪Semigroup≫ ⟫ .∂ S T .● = Semigroup/Hom S T
⟪ ≪Semigroup≫ ⟫ .∂ S T .∂ F G .● = S.≪Map≫ (S .car) (T .car) ⊧ F .ap ≐ G .ap
⟪ ≪Semigroup≫ ⟫ .∂ S T .∂ F G .∂ α β = G.𝟘
≪Semigroup≫ .idn₀ .ap = C.≪Setoid≫ .idn₀
≪Semigroup≫ .idn₀ {S} .mul = S .car .idn₀
≪Semigroup≫ .cmp₀ F G .ap = C.≪Setoid≫ .cmp₀ (F .ap) (G .ap)
≪Semigroup≫ .cmp₀ {S} {T} {U} F G .mul = U .car .cmp₀ (F .mul) (F .ap .ap₁ (G .mul))
≪Semigroup≫ .idn₁ {S} {T} {F} = C.≪Setoid≫ .idn₁ {S .car} {T .car} {F .ap}
≪Semigroup≫ .cmp₁ {S} {T} {F} {G} {H} = C.≪Setoid≫ .cmp₁ {S .car} {T .car} {F .ap} {G .ap} {H .ap}
≪Semigroup≫ .inv₁ {S} {T} {F} {G} = C.≪Setoid≫ .inv₁ {S .car} {T .car} {F .ap} {G .ap}
≪Semigroup≫ .coh-λ {S} {T} = T .car .idn₀
≪Semigroup≫ .coh-ρ {S} {T} = T .car .idn₀
≪Semigroup≫ .coh-α {S} {T} {U} {V} = V .car .idn₀
≪Semigroup≫ .coh-ω {S} {T} {U} {F} {G} {H} {I} α β = C.≪Setoid≫ .coh-ω {S .car} {T .car} {U .car} {F .ap} {G .ap} {H .ap} {I .ap} α β
