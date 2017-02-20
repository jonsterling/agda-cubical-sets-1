{-# OPTIONS --type-in-type #-}

module Setoid where

open import Prelude
open import Globular
open import Syntax

record Setoid : Set where
  no-eta-equality
  field
    obj : Set
    hom : obj → obj → Set
  field
    idn : ∀ {x} → hom x x
    cmp : ∀ {x y z} → hom y z → hom x y → hom x z
    inv : ∀ {x y} → hom x y → hom y x
open Setoid public
{-# DISPLAY Setoid.idn A = 𝟙 #-}
{-# DISPLAY Setoid.cmp A g f = g ∘ f #-}

record Map (𝒳 𝒴 : Setoid) : Set where
  no-eta-equality
  field
    ap₀ : obj 𝒳 → obj 𝒴
    ap₁ : ∀ {x y} → hom 𝒳 x y → hom 𝒴 (ap₀ x) (ap₀ y)
open Map public
{-# DISPLAY Map.ap₀ F x = F x #-}
{-# DISPLAY Map.ap₁ F f = F f #-}

≪Map≫ : Setoid → Setoid → Setoid
≪Map≫ 𝒳 𝒴 .obj = Map 𝒳 𝒴
≪Map≫ 𝒳 𝒴 .hom F G = ∀ {x} → hom 𝒴 (ap₀ F x) (ap₀ G x)
≪Map≫ 𝒳 𝒴 .idn = idn 𝒴
≪Map≫ 𝒳 𝒴 .cmp β α {x} = cmp 𝒴 (β {x}) (α {x})
≪Map≫ 𝒳 𝒴 .inv α {x} = inv 𝒴 (α {x})

open import Category

≪hom≫ : (𝒳 : Category) (x y : ⟪ 𝒳 ⟫ .●) → Setoid
≪hom≫ 𝒳 x y .obj = ⟪ 𝒳 ⟫ .∂ x y .●
≪hom≫ 𝒳 x y .hom f g = ⟪ 𝒳 ⟫ .∂ x y .∂ f g .●
≪hom≫ 𝒳 x y .idn {f} = idn₁ 𝒳
≪hom≫ 𝒳 x y .cmp {f}{g}{h} = cmp₁ 𝒳
≪hom≫ 𝒳 x y .inv {f}{g} = inv₁ 𝒳

≪Setoid≫ : Category
⟪ ≪Setoid≫ ⟫ .● = Setoid
⟪ ≪Setoid≫ ⟫ .∂ 𝒳 𝒴 .● = Map 𝒳 𝒴
⟪ ≪Setoid≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .● = ∀ {x} → hom 𝒴 (ap₀ F x) (ap₀ G x)
⟪ ≪Setoid≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .∂ α β = Void
idn₀ ≪Setoid≫ {𝒳} .ap₀ x = x
idn₀ ≪Setoid≫ {𝒳} .ap₁ f = f
cmp₀ ≪Setoid≫ {𝒳}{𝒴}{𝒵} G F .ap₀ x = ap₀ G (ap₀ F x)
cmp₀ ≪Setoid≫ {𝒳}{𝒴}{𝒵} G F .ap₁ f = ap₁ G (ap₁ F f)
idn₁ ≪Setoid≫ {𝒳}{𝒴}{F}{x} = idn 𝒴
cmp₁ ≪Setoid≫ {𝒳}{𝒴}{F}{G}{H} β α {x} = cmp 𝒴 (β {x}) (α {x})
inv₁ ≪Setoid≫ {𝒳}{𝒴}{F}{G} α {x} = inv 𝒴 (α {x})
cmp₀* ≪Setoid≫ {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} α β {x} = cmp 𝒵 (ap₁ G₁ (β {x})) (α {ap₀ F₀ x})
coh-λ ≪Setoid≫ {𝒳}{𝒴}{F}{x} = idn 𝒴
coh-ρ ≪Setoid≫ {𝒳}{𝒴}{F}{x} = idn 𝒴
coh-α ≪Setoid≫ {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H}{x} = idn 𝒵

≪-∘_≫
  : {𝒳 : Category} {x y z : ⟪ 𝒳 ⟫ .●}
  → (f : 𝒳 ⊧ x ⇾ y)
  → Map (≪hom≫ 𝒳 y z) (≪hom≫ 𝒳 x z)
≪-∘_≫ {𝒳} f .ap₀ g = cmp₀ 𝒳 g f
≪-∘_≫ {𝒳} f .ap₁ {g₀}{g₁} β = cmp₀* 𝒳 β (idn₁ 𝒳)

≪_∘-≫
  : {𝒳 : Category} {x y z : ⟪ 𝒳 ⟫ .●}
  → (g : 𝒳 ⊧ y ⇾ z)
  → Map (≪hom≫ 𝒳 x y) (≪hom≫ 𝒳 x z)
≪_∘-≫ {𝒳} g .ap₀ f = cmp₀ 𝒳 g f
≪_∘-≫ {𝒳} g .ap₁ {f₀}{f₁} α = cmp₀* 𝒳 (idn₁ 𝒳) α

Yo : (𝒳 : Category) → Functor 𝒳 [ Op 𝒳 , ≪Setoid≫ ]
Yo 𝒳 .ap₀ y .ap₀ x = ≪hom≫ 𝒳 x y
Yo 𝒳 .ap₀ y .ap₁ {ξ}{x} f = ≪-∘ f ≫
Yo 𝒳 .ap₀ y .ap₂ {ξ}{x}{f₀}{f₁} α {g} = cmp₀* 𝒳 (idn₁ 𝒳) α
Yo 𝒳 .ap₀ y .coh-idn {x}{f} = coh-ρ 𝒳
Yo 𝒳 .ap₀ y .coh-cmp g f = inv₁ 𝒳 (coh-α 𝒳)
Yo 𝒳 .ap₁ {ξ}{y} g .ap₀ x = ≪ g ∘-≫
Yo 𝒳 .ap₁ {ξ}{y} g .ap₁ {x}{w} f {h} = inv₁ 𝒳 (coh-α 𝒳)
Yo 𝒳 .ap₂ α = cmp₀* 𝒳 α (idn₁ 𝒳)
Yo 𝒳 .coh-idn = coh-λ 𝒳
Yo 𝒳 .coh-cmp g f = coh-α 𝒳
