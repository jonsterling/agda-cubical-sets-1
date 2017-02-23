{-# OPTIONS --type-in-type #-}

module Basis.Setoid.Boot where

open import Basis.Syntax public

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
