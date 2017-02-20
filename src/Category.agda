module Category where

open import Globular
open import Prelude
open import Syntax

record Category : Set where
  no-eta-equality
  field ⟪_⟫ : Globular
  open CellSyntax {⟪_⟫}
  field
    idn₀ : ∀ {x}
      → x ⇾ x
    cmp₀ : ∀ {x y z}
      → (g : y ⇾ z) (f : x ⇾ y)
      → x ⇾ z
    idn₁ : ∀ {x y} {f : x ⇾ y}
      → f ⇔ f
    cmp₁ : ∀ {x y} {f g h : x ⇾ y}
      → (β : g ⇔ h) (α : f ⇔ g)
      → f ⇔ h
    inv₁ : ∀ {x y} {f g : x ⇾ y}
      → (α : f ⇔ g)
      → g ⇔ f
    cmp₀* : ∀ {x y z} {f₀ f₁ : x ⇾ y} {g₀ g₁ : y ⇾ z}
      → (β : g₀ ⇔ g₁) (α : f₀ ⇔ f₁)
      → cmp₀ g₀ f₀ ⇔ cmp₀ g₁ f₁
    coh-λ : ∀ {x y} {f : x ⇾ y}
      → cmp₀ idn₀ f ⇔ f
    coh-ρ : ∀ {x y} {f : x ⇾ y}
      → cmp₀ f idn₀ ⇔ f
    coh-α : ∀ {w x y z} {f : w ⇾ x} {g : x ⇾ y} {h : y ⇾ z}
      → cmp₀ (cmp₀ h g) f ⇔ cmp₀ h (cmp₀ g f)
  infix 0 _⊧_⇾_
  infix 0 _⊧_⇔_
  _⊧_⇾_ = cell ⟪_⟫ 1
  _⊧_⇔_ = cell ⟪_⟫ 2
open Category public
open CellSyntax public
{-# DISPLAY Category.idn₀ A = 𝟙 #-}
{-# DISPLAY Category.cmp₀ A g f = g ∘ f #-}

record Functor (𝒳 𝒴 : Category) : Set where
  no-eta-equality
  field
    ap₀ : ● ⟪ 𝒳 ⟫ → ● ⟪ 𝒴 ⟫
    ap₁ : ∀ {x y} → 𝒳 ⊧ x ⇾ y → 𝒴 ⊧ ap₀ x ⇾ ap₀ y
    ap₂ : ∀ {x y} {f g : 𝒳 ⊧ x ⇾ y} → 𝒳 ⊧ f ⇔ g → 𝒴 ⊧ ap₁ f ⇔ ap₁ g
  field
    coh-idn
      : ∀ {x}
      → 𝒴 ⊧ ap₁ (idn₀ 𝒳 {x}) ⇔ idn₀ 𝒴 {ap₀ x}
    coh-cmp
      : ∀ {x y z}
      → (g : 𝒳 ⊧ y ⇾ z) (f : 𝒳 ⊧ x ⇾ y)
      → 𝒴 ⊧ ap₁ (cmp₀ 𝒳 g f) ⇔ cmp₀ 𝒴 (ap₁ g) (ap₁ f)
open Functor public
{-# DISPLAY Functor.ap₀ F x = F x #-}
{-# DISPLAY Functor.ap₁ F f = F f #-}
{-# DISPLAY Functor.ap₂ F α = F α #-}

record Transform {𝒳 𝒴} (F G : Functor 𝒳 𝒴) : Set where
  no-eta-equality
  field
    ap₀ : ∀ x
      → 𝒴 ⊧ ap₀ F x ⇾ ap₀ G x
    ap₁ : ∀ {x y}
      → (f : 𝒳 ⊧ x ⇾ y)
      → 𝒴 ⊧ cmp₀ 𝒴 (ap₀ y) (ap₁ F f) ⇔ cmp₀ 𝒴 (ap₁ G f) (ap₀ x)
open Transform public
{-# DISPLAY Transform.ap₀ α x = α x #-}
{-# DISPLAY Transform.ap₁ α f = α f #-}

Op : Category → Category
⟪ Op 𝒳 ⟫ .● = ● ⟪ 𝒳 ⟫
⟪ Op 𝒳 ⟫ .∂ x y .● = ⟪ 𝒳 ⟫ .∂ y x .●
⟪ Op 𝒳 ⟫ .∂ x y .∂ f g .● = ⟪ 𝒳 ⟫ .∂ y x .∂ f g .●
⟪ Op 𝒳 ⟫ .∂ x y .∂ f g .∂ α β = ⟪ 𝒳 ⟫ .∂ y x .∂ f g .∂ α β
Op 𝒳 .idn₀ = idn₀ 𝒳
Op 𝒳 .cmp₀ g f = cmp₀ 𝒳 f g
Op 𝒳 .idn₁ = idn₁ 𝒳
Op 𝒳 .cmp₁ = cmp₁ 𝒳
Op 𝒳 .inv₁ = inv₁ 𝒳
Op 𝒳 .cmp₀* α β = cmp₀* 𝒳 β α
Op 𝒳 .coh-λ = coh-ρ 𝒳
Op 𝒳 .coh-ρ = coh-λ 𝒳
Op 𝒳 .coh-α = inv₁ 𝒳 (coh-α 𝒳)

[_,_] : Category → Category → Category
⟪ [ 𝒳 , 𝒴 ] ⟫ .● = Functor 𝒳 𝒴
⟪ [ 𝒳 , 𝒴 ] ⟫ .∂ F G .● = Transform F G
⟪ [ 𝒳 , 𝒴 ] ⟫ .∂ F G .∂ α β .● = ∀ {x} → 𝒴 ⊧ ap₀ α x ⇔ ap₀ β x
⟪ [ 𝒳 , 𝒴 ] ⟫ .∂ F G .∂ α β .∂ 𝔭 𝔮 = Void
[ 𝒳 , 𝒴 ] .idn₀ .ap₀ x = idn₀ 𝒴
[ 𝒳 , 𝒴 ] .idn₀ {F} .ap₁ {x}{y} f = cmp₁ 𝒴 (inv₁ 𝒴 (coh-ρ 𝒴)) (coh-λ 𝒴)
[ 𝒳 , 𝒴 ] .cmp₀ {F}{G}{H} β α .ap₀ x = cmp₀ 𝒴 (ap₀ β x) (ap₀ α x)
[ 𝒳 , 𝒴 ] .cmp₀ {F}{G}{H} β α .ap₁ {x}{y} f =
  cmp₁ 𝒴
    (cmp₁ 𝒴
      (cmp₁ 𝒴
        (cmp₁ 𝒴
          (coh-α 𝒴)
          (cmp₀* 𝒴
            (ap₁ β f)
            (idn₁ 𝒴)))
        (inv₁ 𝒴 (coh-α 𝒴)))
      (cmp₀* 𝒴
        (idn₁ 𝒴)
        (ap₁ α f)))
    (coh-α 𝒴)
[ 𝒳 , 𝒴 ] .idn₁ {F}{G}{α}{x} = idn₁ 𝒴
[ 𝒳 , 𝒴 ] .cmp₁ {F}{G}{α}{β}{γ} q p {x} = cmp₁ 𝒴 (q {x}) (p {x})
[ 𝒳 , 𝒴 ] .inv₁ {F}{G}{α}{β} p {x} = inv₁ 𝒴 (p {x})
[ 𝒳 , 𝒴 ] .cmp₀* {F}{G}{H}{α₀}{α₁}{β₀}{β₁} q p {x} = cmp₀* 𝒴 (q {x}) (p {x})
[ 𝒳 , 𝒴 ] .coh-λ {F}{G}{α}{x} = coh-λ 𝒴
[ 𝒳 , 𝒴 ] .coh-ρ {F}{G}{α}{x} = coh-ρ 𝒴
[ 𝒳 , 𝒴 ] .coh-α {F}{G}{H}{I}{α}{β}{γ}{x} = coh-α 𝒴
