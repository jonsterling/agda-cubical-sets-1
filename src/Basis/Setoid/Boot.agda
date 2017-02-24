{-# OPTIONS --type-in-type #-}

module Basis.Setoid.Boot where

open import Basis.Syntax public

record Setoid : Set where
  no-eta-equality
  field
    obj : Set
    hom : obj → obj → Set
  field
    idn₀ : ∀ {x} → hom x x
    cmp₀ : ∀ {x y z} → hom y z → hom x y → hom x z
    inv₀ : ∀ {x y} → hom x y → hom y x
open Setoid public
{-# DISPLAY Setoid.idn₀ A = ↻ #-}
{-# DISPLAY Setoid.cmp₀ A g f = g ∘ f #-}
