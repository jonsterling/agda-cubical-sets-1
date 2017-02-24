module Basis.Prelude where

open import Basis.Prelude.Bool public
open import Basis.Prelude.Decidable public
open import Basis.Prelude.Finite public
open import Basis.Prelude.Inspect public
open import Basis.Prelude.List public
open import Basis.Prelude.Maybe public
open import Basis.Prelude.Natural public
open import Basis.Prelude.Path public
open import Basis.Prelude.String public
open import Basis.Prelude.Size public
open import Basis.Prelude.Vector public

module T where
  open import Basis.Prelude.Function public
  open import Basis.Prelude.Initial public
  open import Basis.Prelude.Product public
  open import Basis.Prelude.Sum public
  open import Basis.Prelude.Terminal public
open T public
  hiding (idn)
  hiding (cmp)
  hiding (¬_)
  hiding (𝟘)
  hiding (¡)
  hiding (_⊗_)
  hiding (fst)
  hiding (snd)
  hiding (⟨_,_⟩)
  hiding (⟨_⊗_⟩)
  hiding (Σ)
  hiding (_⊕_)
  hiding (inl)
  hiding (inr)
  hiding (𝟙)
  hiding (!)
