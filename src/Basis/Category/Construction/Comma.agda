module Basis.Category.Construction.Comma where

open import Basis.Category.Boot
open import Basis.Category.Functor
open import Basis.Globular

module ↓ where
  record Cell₀
    {𝒳 𝒴 𝒵 : Category}
    (F : Functor 𝒳 𝒵) (G : Functor 𝒴 𝒵)
    : Set where
    no-eta-equality
    constructor cell₀
    field
      {dom₀} : _
      {cod₀} : _
      arr₀ : 𝒵 ⊧ ap₀ F dom₀ ⇾ ap₀ G cod₀
  open Cell₀ public

  record Cell₁
    {𝒳 𝒴 𝒵 : Category}
    {F : Functor 𝒳 𝒵} {G : Functor 𝒴 𝒵}
    (f g : Cell₀ F G)
    : Set where
    no-eta-equality
    constructor cell₁
    field
      {dom₁} : _
      {cod₁} : _
      arr₁ : 𝒵 ⊧ cmp₀ 𝒵 (arr₀ f) (ap₁ F dom₁) ⇔ cmp₀ 𝒵 (ap₁ G cod₁) (arr₀ g)
  open Cell₁ public

  record Cell₂
    {𝒳 𝒴 𝒵 : Category}
    {F : Functor 𝒳 𝒵} {G : Functor 𝒴 𝒵}
    {f g : Cell₀ F G}
    (α β : Cell₁ f g)
    : Set where
    no-eta-equality
    constructor cell₂
    field
      coh-λ : 𝒳 ⊧ dom₁ α ⇔ dom₁ β
      coh-ρ : 𝒴 ⊧ cod₁ α ⇔ cod₁ β
  open Cell₂ public

  [_↓_] : {𝒳 𝒴 𝒵 : Category} (F : Functor 𝒳 𝒵) (G : Functor 𝒴 𝒵) → Category
  ⟪ [_↓_] {𝒳}{𝒴}{𝒵} F G ⟫ .● = Cell₀ F G
  ⟪ [_↓_] {𝒳}{𝒴}{𝒵} F G ⟫ .∂ f g .● = Cell₁ f g
  ⟪ [_↓_] {𝒳}{𝒴}{𝒵} F G ⟫ .∂ f g .∂ α β .● = Cell₂ α β
  ⟪ [_↓_] {𝒳}{𝒴}{𝒵} F G ⟫ .∂ f g .∂ α β .∂ 𝔭 𝔮 = G.𝟘
  [_↓_] {𝒳}{𝒴}{𝒵} F G .idn₀ {x} .dom₁ = idn₀ 𝒳
  [_↓_] {𝒳}{𝒴}{𝒵} F G .idn₀ {x} .cod₁ = idn₀ 𝒴
  [_↓_] {𝒳}{𝒴}{𝒵} F G .idn₀ {x} .arr₁ =
    cmp₁ 𝒵
      (cmp₁ 𝒵
        (inv₁ 𝒵
          (cmp₁ 𝒵
            (coh-λ 𝒵)
            (coh-ω-λ 𝒵 (coh-idn G))))
        (coh-ρ 𝒵))
      (coh-ω-ρ 𝒵 (coh-idn F))
  [_↓_] {𝒳}{𝒴}{𝒵} F G .cmp₀ {f}{g}{h} β α .dom₁ = cmp₀ 𝒳 (dom₁ α) (dom₁ β)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .cmp₀ {f}{g}{h} β α .cod₁ = cmp₀ 𝒴 (cod₁ α) (cod₁ β)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .cmp₀ {f}{g}{h} β α .arr₁ =
    cmp₁ 𝒵
      (cmp₁ 𝒵
        (cmp₁ 𝒵
          (cmp₁ 𝒵
            (cmp₁ 𝒵
              (inv₁ 𝒵
                (cmp₁ 𝒵
                  (coh-α 𝒵)
                  (coh-ω-λ 𝒵 (coh-cmp G (cod₁ α) (cod₁ β)))))
              (coh-ω-ρ 𝒵 (arr₁ β)))
            (coh-α 𝒵))
          (coh-ω-λ 𝒵 (arr₁ α)))
        (inv₁ 𝒵 (coh-α 𝒵)))
      (coh-ω-ρ 𝒵 (coh-cmp F (dom₁ α) (dom₁ β)))
  [_↓_] {𝒳}{𝒴}{𝒵} F G .idn₁ .coh-λ = idn₁ 𝒳
  [_↓_] {𝒳}{𝒴}{𝒵} F G .idn₁ .coh-ρ = idn₁ 𝒴
  [_↓_] {𝒳}{𝒴}{𝒵} F G .cmp₁ 𝔮 𝔭 .coh-λ = cmp₁ 𝒳 (coh-λ 𝔮) (coh-λ 𝔭)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .cmp₁ 𝔮 𝔭 .coh-ρ = cmp₁ 𝒴 (coh-ρ 𝔮) (coh-ρ 𝔭)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .inv₁ 𝔭 .coh-λ = inv₁ 𝒳 (coh-λ 𝔭)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .inv₁ 𝔭 .coh-ρ = inv₁ 𝒴 (coh-ρ 𝔭)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-λ .coh-λ = coh-ρ 𝒳
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-λ .coh-ρ = coh-ρ 𝒴
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-ρ .coh-λ = coh-λ 𝒳
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-ρ .coh-ρ = coh-λ 𝒴
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-α .coh-λ = inv₁ 𝒳 (coh-α 𝒳)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-α .coh-ρ = inv₁ 𝒴 (coh-α 𝒴)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-ω 𝔮 𝔭 .coh-λ = coh-ω 𝒳 (coh-λ 𝔭) (coh-λ 𝔮)
  [_↓_] {𝒳}{𝒴}{𝒵} F G .coh-ω 𝔮 𝔭 .coh-ρ = coh-ω 𝒴 (coh-ρ 𝔭) (coh-ρ 𝔮)
open ↓ public
  using ([_↓_])
