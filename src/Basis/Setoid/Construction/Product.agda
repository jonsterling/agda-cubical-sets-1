module Basis.Setoid.Construction.Product where

open import Basis.Setoid.Boot
open import Basis.Setoid.Map
open import Basis.Prelude

Π : (I : Set) (𝒳 : I → Setoid) → Setoid
Π I 𝒳 .obj = (i : I) → obj (𝒳 i)
Π I 𝒳 .hom f g = (i : I) → hom (𝒳 i) (f i) (g i)
Π I 𝒳 .idn₀ i = idn₀ (𝒳 i)
Π I 𝒳 .cmp₀ q p i = cmp₀ (𝒳 i) (q i) (p i)
Π I 𝒳 .inv₀ p i = inv₀ (𝒳 i) (p i)

_⊗_ : Setoid → Setoid → Setoid
(𝒳 ⊗ 𝒴) .obj = obj 𝒳 T.⊗ obj 𝒴
(𝒳 ⊗ 𝒴) .hom (x₀ , y₀) (x₁ , y₁) = hom 𝒳 x₀ x₁ T.⊗ hom 𝒴 y₀ y₁
(𝒳 ⊗ 𝒴) .idn₀ = idn₀ 𝒳 , idn₀ 𝒴
(𝒳 ⊗ 𝒴) .cmp₀ (f₁ , g₁) (f₀ , g₀) = cmp₀ 𝒳 f₁ f₀ , cmp₀ 𝒴 g₁ g₀
(𝒳 ⊗ 𝒴) .inv₀ (f , g) = inv₀ 𝒳 f , inv₀ 𝒴 g

fst : ∀ {𝒳 𝒴} → Map (𝒳 ⊗ 𝒴) 𝒳
fst .ap₀ = T.fst
fst .ap₁ = T.fst

snd : ∀ {𝒳 𝒴} → Map (𝒳 ⊗ 𝒴) 𝒴
snd .ap₀ = T.snd
snd .ap₁ = T.snd

⟨_,_⟩ : ∀ {𝒳 𝒴 𝒵} (F : Map 𝒵 𝒳) (G : Map 𝒵 𝒴) → Map 𝒵 (𝒳 ⊗ 𝒴)
⟨ F , G ⟩ .ap₀ = T.⟨ ap₀ F , ap₀ G ⟩
⟨ F , G ⟩ .ap₁ = T.⟨ ap₁ F , ap₁ G ⟩

⟨_⊗_⟩ : ∀ {𝒳 𝒴 𝒞 𝒟} (F : Map 𝒳 𝒞) (G : Map 𝒴 𝒟) → Map (𝒳 ⊗ 𝒴) (𝒞 ⊗ 𝒟)
⟨ F ⊗ G ⟩ = ⟨ cmp F fst , cmp G snd ⟩
