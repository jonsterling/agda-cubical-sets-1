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

record Monoid/Hom (M N : Monoid) : Set where
  open Monoid
  field
    ap : S.Map (M .car) (N .car)
    idn : N .car ⊧ ap₀ ap (M .idn) ≐ N .idn
    mul : ∀ {m n} → N .car ⊧ ap₀ ap (ap₀ (M .mul) (m , n)) ≐ ap₀ (N .mul) ((ap₀ ap m) , (ap₀ ap n))


open Semigroup public
open Semigroup/Hom public
open Monoid public
open Monoid/Hom public

Monoid⇒Semigroup : Monoid → Semigroup
Monoid⇒Semigroup M .car = M .car
Monoid⇒Semigroup M .mul = M .mul
Monoid⇒Semigroup M .coh-α = M .coh-α

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

≪Monoid≫ : Category
⟪ ≪Monoid≫ ⟫ .● = Monoid
⟪ ≪Monoid≫ ⟫ .∂ M N .● = Monoid/Hom M N
⟪ ≪Monoid≫ ⟫ .∂ M N .∂ F G .● = S.≪Map≫ (M .car) (N .car) ⊧ F .ap ≐ G .ap
⟪ ≪Monoid≫ ⟫ .∂ M N .∂ F G .∂ α β = G.𝟘
≪Monoid≫ .idn₀ .ap = C.≪Setoid≫ .idn₀
≪Monoid≫ .idn₀ {M} .idn = M .car .idn₀
≪Monoid≫ .idn₀ {M} .mul = M .car .idn₀
≪Monoid≫ .cmp₀ F G .ap = C.≪Setoid≫ .cmp₀ (F .ap) (G .ap)
≪Monoid≫ .cmp₀ {M} {N} {O} F G .idn = O .car .cmp₀ (F .idn) (F .ap .ap₁ (G .idn))
≪Monoid≫ .cmp₀ {M} {N} {O} F G .mul = O .car .cmp₀ (F .mul) (F .ap .ap₁ (G .mul))
≪Monoid≫ .idn₁ {M} {N} {F} = C.≪Setoid≫ .idn₁ {M .car} {N .car} {F .ap}
≪Monoid≫ .cmp₁ {M} {N} {F} {G} {H} = C.≪Setoid≫ .cmp₁ {M .car} {N .car} {F .ap} {G .ap} {H .ap}
≪Monoid≫ .inv₁ {M} {N} {F} {G} = C.≪Setoid≫ .inv₁ {M .car} {N .car} {F .ap} {G .ap}
≪Monoid≫ .coh-λ {M} {N} = N .car .idn₀
≪Monoid≫ .coh-ρ {M} {N} = N .car .idn₀
≪Monoid≫ .coh-α {M} {N} {O} {P} = P .car .idn₀
≪Monoid≫ .coh-ω {M} {N} {O} {F} {G} {H} {I} α β = C.≪Setoid≫ .coh-ω {M .car} {N .car} {O .car} {F .ap} {G .ap} {H .ap} {I .ap} α β

≪Monoid⇒Semigroup≫ : Functor ≪Monoid≫ ≪Semigroup≫
≪Monoid⇒Semigroup≫ .ap₀ = Monoid⇒Semigroup
≪Monoid⇒Semigroup≫ .ap₁ F .ap = F .ap
≪Monoid⇒Semigroup≫ .ap₁ F .mul = F .mul
≪Monoid⇒Semigroup≫ .ap₂ α = α
≪Monoid⇒Semigroup≫ .coh-idn {M} = M .car .idn₀
≪Monoid⇒Semigroup≫ .coh-cmp {M} {N} {O} g f = O .car .idn₀
