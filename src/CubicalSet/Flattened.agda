{-# OPTIONS --type-in-type #-}

module CubicalSet.Flattened where

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
  using (Setoid)
open import Symbol

record □Set : Set where
  field -- setoids fibered over cubes
    obj
      : (Γ : Symbols)
      → Set
    hom
      : ∀ Γ
      → obj Γ → obj Γ → Set
    idn
      : ∀ {Γ x}
      → hom Γ x x
    cmp
      : ∀ {Γ x y z}
      → (q : hom Γ y z)
      → (p : hom Γ x y)
      → hom Γ x z
    inv
      : ∀ {Γ x y}
      → (p : hom Γ x y)
      → hom Γ y x
  field -- substitution across fibers
    sub
      : ∀ {Γ Δ}
      → (f : Sub Δ Γ)
      → obj Γ → obj Δ
    sub-idn
      : ∀ {Γ x}
      → hom Γ (sub loop x) x
    sub-cmp
      : ∀ {Γ Δ Θ x}
      → (g : Sub Θ Δ)
      → (f : Sub Δ Γ)
      → hom Θ (sub (f ≫=≫ g) x) (sub g (sub f x))
    sub-rsp -- functoriality or whiskering
      : ∀ {Γ Δ x y}
      → (f g : Sub Δ Γ)
      → (α : f Cube.≅ g)
      → (β : hom Γ x y)
      → hom Δ (sub f x) (sub g y)
open □Set public

record □Map (𝒳 𝒴 : □Set) : Set where
  no-eta-equality
  field
    ap₀ : ∀ {Γ} → obj 𝒳 Γ → obj 𝒴 Γ
    ap₁ : ∀ {Γ x y} → hom 𝒳 Γ x y → hom 𝒴 Γ (ap₀ x) (ap₀ y)
    ap₂ : ∀ {Γ Δ} (f : Sub Δ Γ) {x} → hom 𝒴 Δ (ap₀ (sub 𝒳 f x)) (sub 𝒴 f (ap₀ x))
open □Map public
{-# DISPLAY □Map.ap₀ 𝒳 x = 𝒳 x #-}
{-# DISPLAY □Map.ap₁ 𝒳 p = 𝒳 p #-}
{-# DISPLAY □Map.ap₂ 𝒳 f = 𝒳 f #-}

≪□Set≫ : Category
⟪ ≪□Set≫ ⟫ .● = □Set
⟪ ≪□Set≫ ⟫ .∂ 𝒳 𝒴 .● = □Map 𝒳 𝒴
⟪ ≪□Set≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .● = ∀ {Γ x} → hom 𝒴 Γ (ap₀ F x) (ap₀ G x)
⟪ ≪□Set≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .∂ α β = Void
≪□Set≫ .idn₀ {𝒳} .ap₀ x = x
≪□Set≫ .idn₀ {𝒳} .ap₁ p = p
≪□Set≫ .idn₀ {𝒳} .ap₂ f = idn 𝒳
≪□Set≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₀ x = ap₀ G (ap₀ F x)
≪□Set≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₁ p = ap₁ G (ap₁ F p)
≪□Set≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₂ f = cmp 𝒵 (ap₂ G f) (ap₁ G (ap₂ F f))
≪□Set≫ .idn₁ {𝒳}{𝒴}{F}{Γ}{x} = idn 𝒴 {Γ} {ap₀ F x}
≪□Set≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α {Γ}{x} = cmp 𝒴 {Γ} (β {Γ}{x}) (α {Γ}{x})
≪□Set≫ .inv₁ {𝒳}{𝒴}{F}{G} α {Γ}{x} = inv 𝒴 {Γ} (α {Γ}{x})
≪□Set≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α {Γ}{x} = cmp 𝒵 {Γ} (β {Γ}{ap₀ F₁ x}) (ap₁ G₀ (α {Γ}{x}))
≪□Set≫ .coh-λ {𝒳}{𝒴}{F}{Γ}{x} = idn 𝒴
≪□Set≫ .coh-ρ {𝒳}{𝒴}{F}{Γ}{x} = idn 𝒴
≪□Set≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H}{Γ}{x} = idn 𝒵

-- the formal or representable cube
□ : Symbols → □Set
□ Δ .obj Γ = Sub Γ Δ
□ Δ .hom Γ = Cube._≅_
□ Δ .idn = 𝕀.idn refl
□ Δ .cmp β α {i} = 𝕀.cmp (β {i}) (α {i})
□ Δ .inv α {i} = 𝕀.inv (α {i})
□ Δ .sub f = λ g → g ≫=≫ f
□ Δ .sub-idn = 𝕀.idn Cube.idn
□ Δ .sub-cmp {x = h} g f {i} = 𝕀.idn (Cube.ass (look h i) f g)
□ Δ .sub-rsp {x = h₀}{h₁} f g α β {i} = Cube.rsp (look h₀ i) (look h₁ i) f g (β {i}) α

-- the interval in HIT style
data Interval (I : Symbols) : Set where
  west : Interval I
  east : Interval I
  walk : (φ : 𝕀 I) → Interval I

interval : □Set
interval .obj = Interval
interval .hom I east east = T.𝟙
interval .hom I east (walk φ₁) = #1 𝕀.≅ φ₁
interval .hom I (walk φ₀) east = φ₀ 𝕀.≅ #1
interval .hom I (walk φ₀) (walk φ₁) = φ₀ 𝕀.≅ φ₁
interval .hom I (walk φ₀) west = φ₀ 𝕀.≅ #0
interval .hom I west (walk φ₁) = #0 𝕀.≅ φ₁
interval .hom I west west = T.𝟙
interval .hom I _ _ = T.𝟘
interval .idn {x = west} = *
interval .idn {x = east} = *
interval .idn {x = walk φ} = 𝕀.idn refl
interval .cmp {x = west} {west} {west} * * = *
interval .cmp {x = west} {west} {east} () *
interval .cmp {x = west} {west} {walk φ₂} q * = q
interval .cmp {x = west} {east} {west} () ()
interval .cmp {x = west} {east} {east} * ()
interval .cmp {x = west} {east} {walk φ₂} q ()
interval .cmp {x = west} {walk φ₁} {west} q p = *
interval .cmp {x = west} {walk φ₁} {east} q p = 𝕀.distinct (𝕀.cmp q p)
interval .cmp {x = west} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
interval .cmp {x = east} {west} {west} * ()
interval .cmp {x = east} {west} {east} () ()
interval .cmp {x = east} {west} {walk φ₂} q ()
interval .cmp {x = east} {east} {west} () *
interval .cmp {x = east} {east} {east} * * = *
interval .cmp {x = east} {east} {walk φ₂} q * = q
interval .cmp {x = east} {walk φ₁} {west} q p = 𝕀.distinct (𝕀.cmp (𝕀.inv p) (𝕀.inv q))
interval .cmp {x = east} {walk φ₁} {east} q p = *
interval .cmp {x = east} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
interval .cmp {x = walk φ₀} {west} {west} * p = p
interval .cmp {x = walk φ₀} {west} {east} () p
interval .cmp {x = walk φ₀} {west} {walk φ₂} q p = 𝕀.cmp q p
interval .cmp {x = walk φ₀} {east} {west} () p
interval .cmp {x = walk φ₀} {east} {east} * p = p
interval .cmp {x = walk φ₀} {east} {walk φ₂} q p = 𝕀.cmp q p
interval .cmp {x = walk φ₀} {walk φ₁} {west} q p = 𝕀.cmp q p
interval .cmp {x = walk φ₀} {walk φ₁} {east} q p = 𝕀.cmp q p
interval .cmp {x = walk φ₀} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
interval .inv {x = west} {west} * = *
interval .inv {x = west} {east} ()
interval .inv {x = west} {walk φ₁} p = 𝕀.inv p
interval .inv {x = east} {west} ()
interval .inv {x = east} {east} * = *
interval .inv {x = east} {walk φ₁} p = 𝕀.inv p
interval .inv {x = walk φ₀} {west} p = 𝕀.inv p
interval .inv {x = walk φ₀} {east} p = 𝕀.inv p
interval .inv {x = walk φ₀} {walk φ₁} p = 𝕀.inv p
interval .sub f west = west
interval .sub f east = east
interval .sub f (walk φ) = walk (φ ≫= f)
interval .sub-idn {x = west} = *
interval .sub-idn {x = east} = *
interval .sub-idn {x = walk φ} = 𝕀.idn Cube.idn
interval .sub-cmp {x = west} g f = *
interval .sub-cmp {x = east} g f = *
interval .sub-cmp {x = walk φ} g f = 𝕀.idn (Cube.ass φ f g)
interval .sub-rsp {x = west} {west} f p α β = *
interval .sub-rsp {x = west} {east} f p α ()
interval .sub-rsp {x = west} {walk φ₁} f p α β = Cube.rsp-lhs p β
interval .sub-rsp {x = east} {west} f p α ()
interval .sub-rsp {x = east} {east} f p α β = *
interval .sub-rsp {x = east} {walk φ₁} f p α β = Cube.rsp-lhs p β
interval .sub-rsp {x = walk φ₀} {west} f p α β = Cube.rsp-lhs f β
interval .sub-rsp {x = walk φ₀} {east} f p α β = Cube.rsp-lhs f β
interval .sub-rsp {x = walk φ₀} {walk φ₁} f p α β = Cube.rsp φ₀ φ₁ f p β α

-- walk "a" ≅ west (under {"a" ≔ #0})
ϕ₀ :
  hom interval []
    (sub interval ("a" ≔ #0 ∷ []) (walk ≪ "a" ≫))
    west
ϕ₀ = 𝕀.idn refl

-- walk (¬ "a" ∨ "b") ≅ east (under {"a" ≔ #0; "b" ≔ #0})
ϕ₁ :
  hom interval []
    (sub interval ("a" ≔ #0 ∷ "b" ≔ #0 ∷ []) (walk (¬ ≪ "a" ≫ ∨ ≪ "b" ≫)))
    east
ϕ₁ = 𝕀.cmp 𝕀.¬-#0 𝕀.∨-uni
