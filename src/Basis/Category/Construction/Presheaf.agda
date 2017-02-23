module Basis.Category.Construction.Presheaf where

open import Basis.Category.Boot
open import Basis.Category.Construction.Functor
open import Basis.Category.Construction.Opposite
open import Basis.Category.Construction.Setoid
open import Basis.Category.Functor

Presheaf : Category → Set
Presheaf 𝒳 = Functor (Op 𝒳) ≪Setoid≫

≪Presheaf≫ : Category → Category
≪Presheaf≫ 𝒳 = [ Op 𝒳 , ≪Setoid≫ ]
