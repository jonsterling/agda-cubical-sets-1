module Basis.Category.Construction.Category where

open import Basis.Category.Boot
open import Basis.Category.Functor
open import Basis.Category.Isomorphism
open import Basis.Category.Transform
open import Basis.Category.Construction.Core
open import Basis.Category.Construction.Functor
open import Basis.Globular

open ≅

≪Category≫ : Category
⟪ ≪Category≫ ⟫ .● = Category
⟪ ≪Category≫ ⟫ .∂ 𝒳 𝒴 .● = Functor 𝒳 𝒴
⟪ ≪Category≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .● = Core [ 𝒳 , 𝒴 ] ⊧ F ⇾ G
⟪ ≪Category≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .∂ α β = G.𝟘
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
      (coh-ω-ρ 𝒴
        (cmp₁ 𝒴
          (cmp₁ 𝒴
            (coh-λ 𝒴)
            (coh-ω-λ 𝒴 (coh-from∘into β)))
          (inv₁ 𝒴 (coh-α 𝒴)))))
    (coh-α 𝒴)
≪Category≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α .coh-into∘from =
  cmp₁ 𝒴
    (cmp₁ 𝒴
      (coh-into∘from β)
      (coh-ω-ρ 𝒴
        (cmp₁ 𝒴
          (cmp₁ 𝒴
            (coh-λ 𝒴)
            (coh-ω-λ 𝒴 (coh-into∘from α)))
          (inv₁ 𝒴 (coh-α 𝒴)))))
    (coh-α 𝒴)
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .into = from α
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .from = into α
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .coh-from∘into = coh-into∘from α
≪Category≫ .inv₁ {𝒳}{𝒴}{F}{G} α .coh-into∘from = coh-from∘into α
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
≪Category≫ .coh-ω {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .into .ap₀ x =
  cmp₀ 𝒵 (ap₀ (into β) (ap₀ F₁ x)) (ap₁ G₀ (ap₀ (into α) x))
≪Category≫ .coh-ω {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .into .ap₁ {x}{y} f =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (cmp₁ 𝒵
        (cmp₁ 𝒵
          (coh-α 𝒵)
          (coh-ω-λ 𝒵
            (ap₁ (into β) (ap₁ F₁ f))))
        (inv₁ 𝒵 (coh-α 𝒵)))
      (coh-ω-ρ 𝒵
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (coh-cmp G₀ (ap₁ F₁ f) (ap₀ (into α) x))
            (ap₂ G₀ (ap₁ (into α) f)))
          (inv₁ 𝒵 (coh-cmp G₀ (ap₀ (into α) y) (ap₁ F₀ f))))))
    (coh-α 𝒵)
≪Category≫ .coh-ω {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .from .ap₀ x =
  cmp₀ 𝒵 (ap₀ (from β) (ap₀ F₀ x)) (ap₁ G₁ (ap₀ (from α) x))
≪Category≫ .coh-ω {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .from .ap₁ {x}{y} f =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (cmp₁ 𝒵
        (cmp₁ 𝒵
          (coh-α 𝒵)
          (coh-ω-λ 𝒵 (ap₁ (from β) (ap₁ F₀ f))))
        (inv₁ 𝒵 (coh-α 𝒵)))
      (coh-ω-ρ 𝒵
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (coh-cmp G₁ (ap₁ F₀ f) (ap₀ (from α) x))
            (ap₂ G₁ (ap₁ (from α) f)))
          (inv₁ 𝒵 (coh-cmp G₁ (ap₀ (from α) y) (ap₁ F₁ f))))))
    (coh-α 𝒵)
≪Category≫ .coh-ω {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .coh-from∘into {x} =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (coh-from∘into β)
      (coh-ω-ρ 𝒵
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (cmp₁ 𝒵
              (coh-λ 𝒵)
              (coh-ω-λ 𝒵
                (cmp₁ 𝒵
                  (cmp₁ 𝒵
                    (coh-idn G₁)
                    (ap₂ G₁ (coh-from∘into α)))
                  (inv₁ 𝒵 (coh-cmp G₁ (ap₀ (from α) x) (ap₀ (into α) x))))))
            (inv₁ 𝒵 (coh-α 𝒵)))
          (coh-ω-ρ 𝒵 (ap₁ (into β) (ap₀ (into α) x))))))
    (coh-α 𝒵)
≪Category≫ .coh-ω {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α .coh-into∘from {x} =
  cmp₁ 𝒵
    (cmp₁ 𝒵
      (coh-into∘from β)
      (coh-ω-ρ 𝒵
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (cmp₁ 𝒵
              (coh-λ 𝒵)
              (coh-ω-λ 𝒵
                (cmp₁ 𝒵
                  (cmp₁ 𝒵
                    (coh-idn G₀)
                    (ap₂ G₀ (coh-into∘from α)))
                  (inv₁ 𝒵 (coh-cmp G₀ (ap₀ (into α) x) (ap₀ (from α) x))))))
            (inv₁ 𝒵 (coh-α 𝒵)))
          (coh-ω-ρ 𝒵 (ap₁ (from β) (ap₀ (from α) x))))))
    (coh-α 𝒵)
