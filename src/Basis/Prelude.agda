module Basis.Prelude where

open import Basis.Prelude.Bool public
open import Basis.Prelude.Decidable public
open import Basis.Prelude.Inspect public
open import Basis.Prelude.List public
open import Basis.Prelude.Maybe public
open import Basis.Prelude.Natural public
open import Basis.Prelude.Path public
open import Basis.Prelude.String public

module T where
  open import Basis.Prelude.Product public
  open import Basis.Prelude.Sum public
  open import Basis.Prelude.Initial public
  open import Basis.Prelude.Terminal public
open T public
  hiding (_⊗_)
  hiding (fst)
  hiding (snd)
  hiding (⟨_,_⟩)
  hiding (_⊕_)
  hiding (¬_)
  hiding (𝟘)
  hiding (𝟙)
