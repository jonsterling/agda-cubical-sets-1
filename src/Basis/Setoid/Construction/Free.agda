module Basis.Setoid.Construction.Free where

open import Basis.Setoid.Boot
open import Basis.Prelude

module Free {A : Set} (Ψ : A → A → Set) where
  data ⊢[_] (x : A) : A → Set where
    ▸emb
      : ∀ {y}
      → (f : Ψ x y)
      → ⊢[_] x y
    ▸idn
      : ⊢[_] x x
    ▸cmp
      : ∀ {y z}
      → (q : ⊢[_] y z)
      → (p : ⊢[_] x y)
      → ⊢[_] x z
    ▸inv
      : ∀ {y}
      → (p : ⊢[_] y x)
      → ⊢[_] x y

  Free : Setoid
  Free .obj = A
  Free .hom = ⊢[_]
  Free .idn₀ = ▸idn
  Free .cmp₀ = ▸cmp
  Free .inv₀ = ▸inv
open Free public
  using (Free)
  using (▸emb)
  using (▸idn)
  using (▸cmp)
  using (▸inv)
