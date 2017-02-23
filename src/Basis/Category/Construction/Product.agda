module Basis.Category.Construction.Product where

open import Basis.Category.Boot
open import Basis.Category.Construction.Category
open import Basis.Category.Functor
open import Basis.Globular
open import Basis.Prelude

infixr 1 _⊗_

_⊗_ : Category → Category → Category
⟪ 𝒳 ⊗ 𝒴 ⟫ .● =
  ⟪ 𝒳 ⟫ .● T.⊗ ⟪ 𝒴 ⟫ .●
⟪ 𝒳 ⊗ 𝒴 ⟫ .∂ (x₀ , y₀) (x₁ , y₁) .● =
  (𝒳 ⊧ x₀ ⇾ x₁) T.⊗ (𝒴 ⊧ y₀ ⇾ y₁)
⟪ 𝒳 ⊗ 𝒴 ⟫ .∂ (x₀ , y₀) (x₁ , y₁) .∂ (f₀ , g₀) (f₁ , g₁) .● =
  (𝒳 ⊧ f₀ ⇔ f₁) T.⊗ (𝒴 ⊧ g₀ ⇔ g₁)
⟪ 𝒳 ⊗ 𝒴 ⟫ .∂ x y .∂ f g .∂ α β = G.𝟘
(𝒳 ⊗ 𝒴) .idn₀ =
  idn₀ 𝒳 , idn₀ 𝒴
(𝒳 ⊗ 𝒴) .cmp₀ (f₁ , g₁) (f₀ , g₀) =
  cmp₀ 𝒳 f₁ f₀ , cmp₀ 𝒴 g₁ g₀
(𝒳 ⊗ 𝒴) .idn₁ =
  idn₁ 𝒳 , idn₁ 𝒴
(𝒳 ⊗ 𝒴) .cmp₁ (α₁ , β₁) (α₀ , β₀) =
  cmp₁ 𝒳 α₁ α₀ , cmp₁ 𝒴 β₁ β₀
(𝒳 ⊗ 𝒴) .inv₁ (α , β) =
  inv₁ 𝒳 α , inv₁ 𝒴 β
(𝒳 ⊗ 𝒴) .cmp₀* (α₁ , β₁) (α₀ , β₀) =
  cmp₀* 𝒳 α₁ α₀ , cmp₀* 𝒴 β₁ β₀
(𝒳 ⊗ 𝒴) .coh-λ =
  coh-λ 𝒳 , coh-λ 𝒴
(𝒳 ⊗ 𝒴) .coh-ρ =
  coh-ρ 𝒳 , coh-ρ 𝒴
(𝒳 ⊗ 𝒴) .coh-α =
  coh-α 𝒳 , coh-α 𝒴

fst : ∀ {𝒳 𝒴} → Functor (𝒳 ⊗ 𝒴) 𝒳
fst .ap₀ = T.fst
fst .ap₁ = T.fst
fst .ap₂ = T.fst
fst {𝒳}{𝒴} .coh-idn = idn₁ 𝒳
fst {𝒳}{𝒴} .coh-cmp g f = idn₁ 𝒳

snd : ∀ {𝒳 𝒴} → Functor (𝒳 ⊗ 𝒴) 𝒴
snd .ap₀ = T.snd
snd .ap₁ = T.snd
snd .ap₂ = T.snd
snd {𝒳}{𝒴} .coh-idn = idn₁ 𝒴
snd {𝒳}{𝒴} .coh-cmp g f = idn₁ 𝒴

⟨_,_⟩
  : ∀ {𝒳 𝒴 𝒵}
  → Functor 𝒳 𝒴
  → Functor 𝒳 𝒵
  → Functor 𝒳 (𝒴 ⊗ 𝒵)
⟨ F , G ⟩ .ap₀ = T.⟨ ap₀ F , ap₀ G ⟩
⟨ F , G ⟩ .ap₁ = T.⟨ ap₁ F , ap₁ G ⟩
⟨ F , G ⟩ .ap₂ = T.⟨ ap₂ F , ap₂ G ⟩
⟨ F , G ⟩ .coh-idn = coh-idn F , coh-idn G
⟨ F , G ⟩ .coh-cmp g f = coh-cmp F g f , coh-cmp G g f

⟨_⊗_⟩
  : ∀ {𝒳 𝒴 𝒞 𝒟}
  → Functor 𝒳 𝒞
  → Functor 𝒴 𝒟
  → Functor (𝒳 ⊗ 𝒴) (𝒞 ⊗ 𝒟)
⟨ F ⊗ G ⟩ = ⟨ cmp₀ ≪Category≫ F fst , cmp₀ ≪Category≫ G snd ⟩

Δ : ∀ {𝒳} → Functor 𝒳 (𝒳 ⊗ 𝒳)
Δ = ⟨ idn₀ ≪Category≫ , idn₀ ≪Category≫ ⟩
