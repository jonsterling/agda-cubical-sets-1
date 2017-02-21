{-# OPTIONS --type-in-type #-}

module Main where

open import Category
open import Cube
  hiding (idn)
open import CubicalSet.Flattened as Flattened
open import CubicalSet.Presheaf as Presheaf
open import DeMorgan as 𝕀
  hiding (idn)
  hiding (cmp)
  hiding (inv)
open import Prelude
open import Setoid
  hiding (module Setoid)

module Equivalence where
  open Setoid

  fwd : Presheaf.□Set → Flattened.□Set
  fwd F .obj Γ = obj (ap₀ F Γ)
  fwd F .hom Γ = hom (ap₀ F Γ)
  fwd F .idn {Γ} = idn (ap₀ F Γ)
  fwd F .cmp {Γ} = cmp (ap₀ F Γ)
  fwd F .inv {Γ} = inv (ap₀ F Γ)
  fwd F .sub f = ap₀ (ap₁ F f)
  fwd F .sub-idn = coh-idn F
  fwd F .sub-cmp g f = coh-cmp F g f
  fwd F .sub-rsp {Γ}{Δ} f g α β = cmp (ap₀ F Δ) (ap₂ F α) (ap₁ (ap₁ F f) β)

  bwd : Flattened.□Set → Presheaf.□Set
  bwd F .ap₀ Γ .obj = obj F Γ
  bwd F .ap₀ Γ .hom = hom F Γ
  bwd F .ap₀ Γ .idn = idn F
  bwd F .ap₀ Γ .cmp = cmp F
  bwd F .ap₀ Γ .inv = inv F
  bwd F .ap₁ f .ap₀ x = sub F f x
  bwd F .ap₁ f .ap₁ α = sub-rsp F f f (𝕀.idn refl) α
  bwd F .ap₂ {Γ}{Δ}{f}{g} α = sub-rsp F f g α (idn F)
  bwd F .coh-idn = sub-idn F
  bwd F .coh-cmp g f = sub-cmp F g f

  iso : ≪Category≫ ⊧ Presheaf.≪□Set≫ ≅ Flattened.≪□Set≫
  iso .into .ap₀ 𝒳 = fwd 𝒳
  iso .into .ap₁ {𝒳}{𝒴} F .ap₀ {Γ} x = ap₀ (ap₀ F Γ) x
  iso .into .ap₁ {𝒳}{𝒴} F .ap₁ {Γ}{x}{y} p = ap₁ (ap₀ F Γ) p
  iso .into .ap₁ {𝒳}{𝒴} F .ap₂ {Γ}{Δ} f {x} = ap₁ F f {x}
  iso .into .ap₂ {𝒳}{𝒴}{F}{G} α {Γ}{x} = α {Γ}{x}
  iso .into .coh-idn {𝒳}{Γ}{x} = idn (ap₀ 𝒳 Γ)
  iso .into .coh-cmp {𝒳}{𝒴}{𝒵} g f {Γ}{x} = idn (ap₀ 𝒵 Γ)
  iso .from .ap₀ 𝒳 = bwd 𝒳
  iso .from .ap₁ {𝒳}{𝒴} F .ap₀ Γ .ap₀ x = ap₀ F x
  iso .from .ap₁ {𝒳}{𝒴} F .ap₀ Γ .ap₁ {x}{y} p = ap₁ F p
  iso .from .ap₁ {𝒳}{𝒴} F .ap₁ {Γ}{Δ} f {x} = ap₂ F f
  iso .from .ap₂ {𝒳}{𝒴}{F}{G} α {Γ}{x} = α {Γ}{x}
  iso .from .coh-idn {𝒳}{Γ}{x} = idn 𝒳
  iso .from .coh-cmp {𝒳}{𝒴}{𝒵} g f {Γ}{x} = idn 𝒵
  iso .coh-from∘into .into .ap₀ 𝒳 .ap₀ Γ .ap₀ x = x
  iso .coh-from∘into .into .ap₀ 𝒳 .ap₀ Γ .ap₁ p = p
  iso .coh-from∘into .into .ap₀ 𝒳 .ap₁ {Γ}{Δ} f {x} = idn (ap₀ 𝒳 Δ)
  iso .coh-from∘into .into .ap₁ {𝒳}{𝒴} f {Γ}{x} = idn (ap₀ 𝒴 Γ)
  iso .coh-from∘into .from .ap₀ 𝒳 .ap₀ Γ .ap₀ x = x
  iso .coh-from∘into .from .ap₀ 𝒳 .ap₀ Γ .ap₁ p = p
  iso .coh-from∘into .from .ap₀ 𝒳 .ap₁ {Γ}{Δ} f {x} = idn (ap₀ 𝒳 Δ)
  iso .coh-from∘into .from .ap₁ {𝒳}{𝒴} f {Γ}{x} = idn (ap₀ 𝒴 Γ)
  iso .coh-from∘into .coh-from∘into {𝒳}{Γ}{x} = idn (ap₀ 𝒳 Γ)
  iso .coh-from∘into .coh-into∘from {𝒳}{Γ}{x} = idn (ap₀ 𝒳 Γ)
  iso .coh-into∘from .into .ap₀ 𝒳 .ap₀ {Γ} x = x
  iso .coh-into∘from .into .ap₀ 𝒳 .ap₁ {Γ}{x}{y} p = p
  iso .coh-into∘from .into .ap₀ 𝒳 .ap₂ {Γ}{Δ} f {x} = idn 𝒳
  iso .coh-into∘from .into .ap₁ {𝒳}{𝒴} f {Γ}{x} = idn 𝒴
  iso .coh-into∘from .from .ap₀ 𝒳 .ap₀ {Γ} x = x
  iso .coh-into∘from .from .ap₀ 𝒳 .ap₁ {Γ}{x}{y} p = p
  iso .coh-into∘from .from .ap₀ 𝒳 .ap₂ {Γ}{Δ} f {x} = idn 𝒳
  iso .coh-into∘from .from .ap₁ {𝒳}{𝒴} f {Γ}{x} = idn 𝒴
  iso .coh-into∘from .coh-from∘into {𝒳}{Γ}{x} = idn 𝒳
  iso .coh-into∘from .coh-into∘from {𝒳}{Γ}{x} = idn 𝒳
