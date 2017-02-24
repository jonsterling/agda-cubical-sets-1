module Main where

open import Basis
open import Cubical

module Equivalence where
  open ≅
  open Flattened

  fwd : Presheaf.□Set → Flattened.□Set
  fwd F .obj Γ = obj (ap₀ F Γ)
  fwd F .hom Γ = hom (ap₀ F Γ)
  fwd F .idn = idn₀ (ap₀ F _)
  fwd F .cmp = cmp₀ (ap₀ F _)
  fwd F .inv = inv₀ (ap₀ F _)
  fwd F .sub f = ap₀ (ap₁ F f)
  fwd F .sub-idn = coh-idn F
  fwd F .sub-cmp g f = coh-cmp F g f
  fwd F .sub-rsp α β = cmp₀ (ap₀ F _) (ap₂ F α) (ap₁ (ap₁ F _) β)

  bwd : Flattened.□Set → Presheaf.□Set
  bwd F .ap₀ Γ .obj = obj F Γ
  bwd F .ap₀ Γ .hom = hom F Γ
  bwd F .ap₀ Γ .idn₀ = idn F
  bwd F .ap₀ Γ .cmp₀ = cmp F
  bwd F .ap₀ Γ .inv₀ = inv F
  bwd F .ap₁ f .ap₀ x = sub F f x
  bwd F .ap₁ f .ap₁ α = sub-rsp F (idn₀ (Sub.set _ _)) α
  bwd F .ap₂ α = sub-rsp F α (idn F)
  bwd F .coh-idn = sub-idn F
  bwd F .coh-cmp g f = sub-cmp F g f

  iso : C.≪Category≫ ⊧ Presheaf.≪□Set≫ ≅ Flattened.≪□Set≫
  iso .into .ap₀ 𝒳 = fwd 𝒳
  iso .into .ap₁ F .ap₀ x = ap₀ (ap₀ F _) x
  iso .into .ap₁ F .ap₁ p = ap₁ (ap₀ F _) p
  iso .into .ap₁ F .ap₂ f = ap₁ F f
  iso .into .ap₂ α = α
  iso .into .coh-idn {x = 𝒳} = idn₀ (ap₀ 𝒳 _)
  iso .into .coh-cmp {z = 𝒵} g f = idn₀ (ap₀ 𝒵 _)
  iso .from .ap₀ 𝒳 = bwd 𝒳
  iso .from .ap₁ F .ap₀ Γ .ap₀ x = ap₀ F x
  iso .from .ap₁ F .ap₀ Γ .ap₁ p = ap₁ F p
  iso .from .ap₁ F .ap₁ f = ap₂ F f
  iso .from .ap₂ α = α
  iso .from .coh-idn {x = 𝒳} = idn 𝒳
  iso .from .coh-cmp {z = 𝒵} g f = idn 𝒵
  iso .coh-from∘into .into .ap₀ 𝒳 .ap₀ Γ .ap₀ x = x
  iso .coh-from∘into .into .ap₀ 𝒳 .ap₀ Γ .ap₁ p = p
  iso .coh-from∘into .into .ap₀ 𝒳 .ap₁ f = idn₀ (ap₀ 𝒳 _)
  iso .coh-from∘into .into .ap₁ {y = 𝒴} f = idn₀ (ap₀ 𝒴 _)
  iso .coh-from∘into .from .ap₀ 𝒳 .ap₀ Γ .ap₀ x = x
  iso .coh-from∘into .from .ap₀ 𝒳 .ap₀ Γ .ap₁ p = p
  iso .coh-from∘into .from .ap₀ 𝒳 .ap₁ f = idn₀ (ap₀ 𝒳 _)
  iso .coh-from∘into .from .ap₁ {y = 𝒴} f = idn₀ (ap₀ 𝒴 _)
  iso .coh-from∘into .coh-from∘into {x = 𝒳}= idn₀ (ap₀ 𝒳 _)
  iso .coh-from∘into .coh-into∘from {x = 𝒳} = idn₀ (ap₀ 𝒳 _)
  iso .coh-into∘from .into .ap₀ 𝒳 .ap₀ x = x
  iso .coh-into∘from .into .ap₀ 𝒳 .ap₁ p = p
  iso .coh-into∘from .into .ap₀ 𝒳 .ap₂ f = idn 𝒳
  iso .coh-into∘from .into .ap₁ {y = 𝒴} f = idn 𝒴
  iso .coh-into∘from .from .ap₀ 𝒳 .ap₀ x = x
  iso .coh-into∘from .from .ap₀ 𝒳 .ap₁ p = p
  iso .coh-into∘from .from .ap₀ 𝒳 .ap₂ f = idn 𝒳
  iso .coh-into∘from .from .ap₁ {y = 𝒴} f = idn 𝒴
  iso .coh-into∘from .coh-from∘into {x = 𝒳} = idn 𝒳
  iso .coh-into∘from .coh-into∘from {x = 𝒳} = idn 𝒳
