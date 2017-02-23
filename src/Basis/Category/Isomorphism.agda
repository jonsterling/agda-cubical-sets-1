module Basis.Category.Isomorphism where

open import Basis.Category.Boot
open import Basis.Globular

module ≅ where
  infix 0 _⊧_≅_
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
open ≅ public
  hiding (module Isomorphism)
  using (Isomorphism)
  using (_⊧_≅_)
