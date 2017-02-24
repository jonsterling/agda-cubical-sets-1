module Basis.Setoid where

open import Basis.Setoid.Boot public

module S where
  open import Basis.Setoid.Boot public
  open import Basis.Setoid.Construction.Coequalizer public
  open import Basis.Setoid.Construction.Coproduct public
  open import Basis.Setoid.Construction.Equalizer public
  open import Basis.Setoid.Construction.Free public
  open import Basis.Setoid.Construction.Hom public
  open import Basis.Setoid.Construction.Initial public
  open import Basis.Setoid.Construction.Map public
  open import Basis.Setoid.Construction.Product public
  open import Basis.Setoid.Construction.Pullback public
  open import Basis.Setoid.Construction.Pushout public
  open import Basis.Setoid.Construction.Terminal public
  open import Basis.Setoid.Map public
open S public
  hiding (Coequalizer)
  hiding (Σ)
  hiding (_⊕_)
  hiding (inl)
  hiding (inr)
  hiding ([_,_])
  hiding ([_⊕_])
  hiding (Equalizer)
  hiding (𝟘)
  hiding (¡)
  hiding (idn)
  hiding (cmp)
  hiding (Π)
  hiding (_⊗_)
  hiding (fst)
  hiding (snd)
  hiding (⟨_,_⟩)
  hiding (⟨_⊗_⟩)
  hiding (Pullback)
  hiding (Pushout)
  hiding (𝟙)
  hiding (!)
