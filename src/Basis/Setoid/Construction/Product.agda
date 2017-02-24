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
𝒳 ⊗ 𝒴 = Π (𝔽 2) (Vector.look (𝒳 ∷ 𝒴 ∷ []))

fst : ∀ {𝒳 𝒴} → Map (𝒳 ⊗ 𝒴) 𝒳
fst .ap₀ x = x zero
fst .ap₁ f = f zero

snd : ∀ {𝒳 𝒴} → Map (𝒳 ⊗ 𝒴) 𝒴
snd .ap₀ x = x (succ zero)
snd .ap₁ f = f (succ zero)

⟨_,_⟩ : ∀ {𝒳 𝒴 𝒵} (F : Map 𝒵 𝒳) (G : Map 𝒵 𝒴) → Map 𝒵 (𝒳 ⊗ 𝒴)
⟨ F , G ⟩ .ap₀ z zero = ap₀ F z
⟨ F , G ⟩ .ap₀ z (succ zero) = ap₀ G z
⟨ F , G ⟩ .ap₀ z (succ (succ ()))
⟨ F , G ⟩ .ap₁ f zero = ap₁ F f
⟨ F , G ⟩ .ap₁ f (succ zero) = ap₁ G f
⟨ F , G ⟩ .ap₁ f (succ (succ ()))

⟨_⊗_⟩ : ∀ {𝒳 𝒴 𝒞 𝒟} (F : Map 𝒳 𝒞) (G : Map 𝒴 𝒟) → Map (𝒳 ⊗ 𝒴) (𝒞 ⊗ 𝒟)
⟨ F ⊗ G ⟩ = ⟨ cmp F fst , cmp G snd ⟩
