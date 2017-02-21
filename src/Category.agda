module Category where

open import Globular
open import Prelude
open import Syntax

infix 0 _⊧_≅_

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

record Isomorphism (𝒳 : Category) (x y : ● ⟪ 𝒳 ⟫) : Set where
  no-eta-equality
  field
    into : 𝒳 ⊧ x ⇾ y
    from : 𝒳 ⊧ y ⇾ x
    coh-from∘into : 𝒳 ⊧ cmp₀ 𝒳 from into ⇔ idn₀ 𝒳 {x}
    coh-into∘from : 𝒳 ⊧ cmp₀ 𝒳 into from ⇔ idn₀ 𝒳 {y}
open Isomorphism public
_⊧_≅_ : (𝒳 : Category) (x y : ● ⟪ 𝒳 ⟫) → Set
_⊧_≅_ = Isomorphism
{-# DISPLAY Isomorphism 𝒳 x y = 𝒳 ⊧ x ≅ y #-}

Core : Category → Category
⟪ Core 𝒳 ⟫ .● = ⟪ 𝒳 ⟫ .●
⟪ Core 𝒳 ⟫ .∂ x y .● = 𝒳 ⊧ x ≅ y
⟪ Core 𝒳 ⟫ .∂ x y .∂ f g .● = 𝒳 ⊧ into f ⇔ into g
⟪ Core 𝒳 ⟫ .∂ x y .∂ f g .∂ α β = Void
Core 𝒳 .idn₀ .into = idn₀ 𝒳
Core 𝒳 .idn₀ .from = idn₀ 𝒳
Core 𝒳 .idn₀ .coh-from∘into = coh-λ 𝒳
Core 𝒳 .idn₀ .coh-into∘from = coh-λ 𝒳
Core 𝒳 .cmp₀ g f .into = cmp₀ 𝒳 (into g) (into f)
Core 𝒳 .cmp₀ g f .from = cmp₀ 𝒳 (from f) (from g)
Core 𝒳 .cmp₀ g f .coh-from∘into =
  cmp₁ 𝒳
    (cmp₁ 𝒳
      (coh-from∘into f)
      (cmp₀* 𝒳
        (idn₁ 𝒳)
        (cmp₁ 𝒳
          (cmp₁ 𝒳
            (coh-λ 𝒳)
            (cmp₀* 𝒳
              (coh-from∘into g)
              (idn₁ 𝒳)))
          (inv₁ 𝒳 (coh-α 𝒳)))))
    (coh-α 𝒳)
Core 𝒳 .cmp₀ g f .coh-into∘from =
  cmp₁ 𝒳
    (cmp₁ 𝒳
      (coh-into∘from g)
      (cmp₀* 𝒳
        (idn₁ 𝒳)
        (cmp₁ 𝒳
          (cmp₁ 𝒳
            (coh-λ 𝒳)
            (cmp₀* 𝒳
              (coh-into∘from f)
              (idn₁ 𝒳)))
          (inv₁ 𝒳 (coh-α 𝒳)))))
    (coh-α 𝒳)
Core 𝒳 .idn₁ = idn₁ 𝒳
Core 𝒳 .cmp₁ = cmp₁ 𝒳
Core 𝒳 .inv₁ = inv₁ 𝒳
Core 𝒳 .cmp₀* = cmp₀* 𝒳
Core 𝒳 .coh-λ = coh-λ 𝒳
Core 𝒳 .coh-ρ = coh-ρ 𝒳
Core 𝒳 .coh-α = coh-α 𝒳

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

≪Category≫ : Category
⟪ ≪Category≫ ⟫ .● = Category
⟪ ≪Category≫ ⟫ .∂ 𝒳 𝒴 .● = Functor 𝒳 𝒴
⟪ ≪Category≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .● = Core [ 𝒳 , 𝒴 ] ⊧ F ⇾ G
⟪ ≪Category≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .∂ α β = Void
≪Category≫ .idn₀ .ap₀ x = x
≪Category≫ .idn₀ .ap₁ f = f
≪Category≫ .idn₀ .ap₂ p = p
≪Category≫ .idn₀ {𝒳} .coh-idn = idn₁ 𝒳
≪Category≫ .idn₀ {𝒳} .coh-cmp g f = idn₁ 𝒳
≪Category≫ .cmp₀ G F .ap₀ x = ap₀ G (ap₀ F x)
≪Category≫ .cmp₀ G F .ap₁ f = ap₁ G (ap₁ F f)
≪Category≫ .cmp₀ G F .ap₂ p = ap₂ G (ap₂ F p)
≪Category≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .coh-idn = cmp₁ 𝒵 (coh-idn G) (ap₂ G (coh-idn F))
≪Category≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .coh-cmp g f = cmp₁ 𝒵 (coh-cmp G (ap₁ F g) (ap₁ F f)) (ap₂ G (coh-cmp F g f))
≪Category≫ .idn₁ {𝒳}{𝒴}{F} .into = idn₀ [ 𝒳 , 𝒴 ]
≪Category≫ .idn₁ {𝒳}{𝒴} .from = idn₀ [ 𝒳 , 𝒴 ]
≪Category≫ .idn₁ {𝒳}{𝒴} .coh-from∘into = coh-λ 𝒴
≪Category≫ .idn₁ {𝒳}{𝒴} .coh-into∘from = coh-λ 𝒴
≪Category≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α .into = cmp₀ [ 𝒳 , 𝒴 ] (into β) (into α)
≪Category≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α .from = cmp₀ [ 𝒳 , 𝒴 ] (from α) (from β)
≪Category≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α .coh-from∘into =
  cmp₁ 𝒴
    (cmp₁ 𝒴
      (coh-from∘into α)
      (cmp₀* 𝒴
        (idn₁ 𝒴)
        (cmp₁ 𝒴
          (cmp₁ 𝒴
            (coh-λ 𝒴)
            (cmp₀* 𝒴
              (coh-from∘into β)
              (idn₁ 𝒴)))
          (inv₁ 𝒴 (coh-α 𝒴)))))
    (coh-α 𝒴)
≪Category≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α .coh-into∘from =
  cmp₁ 𝒴
    (cmp₁ 𝒴
      (coh-into∘from β)
      (cmp₀* 𝒴
        (idn₁ 𝒴)
        (cmp₁ 𝒴
          (cmp₁ 𝒴
            (coh-λ 𝒴)
            (cmp₀* 𝒴
              (coh-into∘from α)
              (idn₁ 𝒴)))
          (inv₁ 𝒴 (coh-α 𝒴)))))
    (coh-α 𝒴)
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .into = from α
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .from = into α
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .coh-from∘into = coh-into∘from α
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .coh-into∘from = coh-from∘into α
≪Category≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .into .ap₀ x =
  cmp₀ 𝒵 (ap₀ (into β) (ap₀ F₁ x)) (ap₁ G₀ (ap₀ (into α) x))
≪Category≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .into .ap₁ {x}{y} f =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (cmp₁ 𝒵
        (cmp₁ 𝒵
          (coh-α 𝒵)
          (cmp₀* 𝒵
            (ap₁ (into β) (ap₁ F₁ f))
            (idn₁ 𝒵)))
        (inv₁ 𝒵 (coh-α 𝒵)))
      (cmp₀* 𝒵
        (idn₁ 𝒵)
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (coh-cmp G₀ (ap₁ F₁ f) (ap₀ (into α) x))
            (ap₂ G₀ (ap₁ (into α) f)))
          (inv₁ 𝒵 (coh-cmp G₀ (ap₀ (into α) y) (ap₁ F₀ f))))))
    (coh-α 𝒵)
≪Category≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .from .ap₀ x =
  cmp₀ 𝒵 (ap₀ (from β) (ap₀ F₀ x)) (ap₁ G₁ (ap₀ (from α) x))
≪Category≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .from .ap₁ {x}{y} f =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (cmp₁ 𝒵
        (cmp₁ 𝒵
          (coh-α 𝒵)
          (cmp₀* 𝒵
            (ap₁ (from β) (ap₁ F₀ f))
            (idn₁ 𝒵)))
        (inv₁ 𝒵 (coh-α 𝒵)))
      (cmp₀* 𝒵
        (idn₁ 𝒵)
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (coh-cmp G₁ (ap₁ F₀ f) (ap₀ (from α) x))
            (ap₂ G₁ (ap₁ (from α) f)))
          (inv₁ 𝒵 (coh-cmp G₁ (ap₀ (from α) y) (ap₁ F₁ f))))))
    (coh-α 𝒵)
≪Category≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .coh-from∘into {x} =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (coh-from∘into β)
      (cmp₀* 𝒵
        (idn₁ 𝒵)
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (cmp₁ 𝒵
              (coh-λ 𝒵)
              (cmp₀* 𝒵
                (cmp₁ 𝒵
                  (cmp₁ 𝒵
                    (coh-idn G₁)
                    (ap₂ G₁ (coh-from∘into α)))
                  (inv₁ 𝒵 (coh-cmp G₁ (ap₀ (from α) x) (ap₀ (into α) x))))
                (idn₁ 𝒵)))
            (inv₁ 𝒵 (coh-α 𝒵)))
          (cmp₀* 𝒵
            (idn₁ 𝒵)
            (ap₁ (into β) (ap₀ (into α) x))))))
    (coh-α 𝒵)
≪Category≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .coh-into∘from {x} =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (coh-into∘from β)
      (cmp₀* 𝒵
        (idn₁ 𝒵)
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (cmp₁ 𝒵
              (coh-λ 𝒵)
              (cmp₀* 𝒵
                (cmp₁ 𝒵
                  (cmp₁ 𝒵
                    (coh-idn G₀)
                    (ap₂ G₀ (coh-into∘from α)))
                  (inv₁ 𝒵 (coh-cmp G₀ (ap₀ (into α) x) (ap₀ (from α) x))))
                (idn₁ 𝒵)))
            (inv₁ 𝒵 (coh-α 𝒵)))
          (cmp₀* 𝒵
            (idn₁ 𝒵)
            (ap₁ (from β) (ap₀ (from α) x))))))
    (coh-α 𝒵)
≪Category≫ .coh-λ {𝒳}{𝒴}{F} .into .ap₀ x = idn₀ 𝒴
≪Category≫ .coh-λ {𝒳}{𝒴}{F} .into .ap₁ f = cmp₁ 𝒴 (inv₁ 𝒴 (coh-ρ 𝒴)) (coh-λ 𝒴)
≪Category≫ .coh-λ {𝒳}{𝒴}{F} .from .ap₀ x = idn₀ 𝒴
≪Category≫ .coh-λ {𝒳}{𝒴}{F} .from .ap₁ f = cmp₁ 𝒴 (inv₁ 𝒴 (coh-ρ 𝒴)) (coh-λ 𝒴)
≪Category≫ .coh-λ {𝒳}{𝒴}{F} .coh-from∘into = coh-λ 𝒴
≪Category≫ .coh-λ {𝒳}{𝒴}{F} .coh-into∘from = coh-λ 𝒴
≪Category≫ .coh-ρ {𝒳}{𝒴}{F} .into .ap₀ x = idn₀ 𝒴
≪Category≫ .coh-ρ {𝒳}{𝒴}{F} .into .ap₁ f = cmp₁ 𝒴 (inv₁ 𝒴 (coh-ρ 𝒴)) (coh-λ 𝒴)
≪Category≫ .coh-ρ {𝒳}{𝒴}{F} .from .ap₀ x = idn₀ 𝒴
≪Category≫ .coh-ρ {𝒳}{𝒴}{F} .from .ap₁ f = cmp₁ 𝒴 (inv₁ 𝒴 (coh-ρ 𝒴)) (coh-λ 𝒴)
≪Category≫ .coh-ρ {𝒳}{𝒴}{F} .coh-from∘into = coh-λ 𝒴
≪Category≫ .coh-ρ {𝒳}{𝒴}{F} .coh-into∘from = coh-λ 𝒴
≪Category≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H} .into .ap₀ x = idn₀ 𝒵
≪Category≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H} .into .ap₁ f = cmp₁ 𝒵 (inv₁ 𝒵 (coh-ρ 𝒵)) (coh-λ 𝒵)
≪Category≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H} .from .ap₀ x = idn₀ 𝒵
≪Category≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H} .from .ap₁ f = cmp₁ 𝒵 (inv₁ 𝒵 (coh-ρ 𝒵)) (coh-λ 𝒵)
≪Category≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H} .coh-from∘into = coh-λ 𝒵
≪Category≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H} .coh-into∘from = coh-λ 𝒵
