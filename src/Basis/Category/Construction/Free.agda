module Basis.Category.Construction.Free where

open import Basis.Category.Boot
open import Basis.Graph
open import Basis.Prelude

module Free (A : Graph) where
  infixl 6 _≫_
  infixl 5 _⋙_

  data Path (x : A .●) : (y : A .●) → Set where
    []
      : Path x x
    _≫_
      : ∀ {y z}
      → (f* : Path x y)
      → (f : A .∂ y z .●)
      → Path x z

  _⋙_
    : ∀ {x y z}
    → Path y z
    → Path x y
    → Path x z
  [] ⋙ f = f
  (g* ≫ g) ⋙ f = (g* ⋙ f) ≫ g

  ⊢coh-ρ
    : ∀ {x y}
    → (f : Path x y)
    → f ⋙ [] ≡ f
  ⊢coh-ρ [] = refl
  ⊢coh-ρ (f* ≫ f) = ≡.ap (λ k → k ≫ f) (⊢coh-ρ f*)

  ⊢coh-α
    : ∀ {w x y z} {f : Path w x} {g : Path x y}
    → (h : Path y z)
    → (h ⋙ g) ⋙ f ≡ h ⋙ (g ⋙ f)
  ⊢coh-α [] = refl
  ⊢coh-α (h* ≫ h) = ≡.ap (λ k → k ≫ h) (⊢coh-α h*)

  Free : Category
  ⟪ Free ⟫ .● = A .●
  ⟪ Free ⟫ .∂ x y .● = Path x y
  ⟪ Free ⟫ .∂ x y .∂ f g = ℼ (f ≡ g)
  Free .idn₀ = []
  Free .cmp₀ = _⋙_
  Free .idn₁ = ≡.idn
  Free .cmp₁ = ≡.cmp
  Free .inv₁ = ≡.inv
  Free .coh-λ = refl
  Free .coh-ρ {f = f} = ⊢coh-ρ f
  Free .coh-α {h = h} = ⊢coh-α h
  Free .coh-ω = ≡.ap² (cmp₀ Free)
open Free public
  using (Free)
