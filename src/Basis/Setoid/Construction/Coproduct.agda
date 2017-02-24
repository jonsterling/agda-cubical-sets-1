module Basis.Setoid.Construction.Coproduct where

open import Basis.Setoid.Boot
open import Basis.Setoid.Map
open import Basis.Prelude

Σ : (I : Set) (𝒳 : I → Setoid) → Setoid
Σ I 𝒳 .obj = T.Σ I λ i → obj (𝒳 i)
Σ I 𝒳 .hom (i ▸ x) (j ▸ y) = T.Σ (i ≡ j) λ {refl → hom (𝒳 i) x y}
Σ I 𝒳 .idn₀ {i ▸ x} = refl ▸ idn₀ (𝒳 i)
Σ I 𝒳 .cmp₀ {i ▸ x}{.i ▸ y}{.i ▸ z} (refl ▸ q) (refl ▸ p) = refl ▸ cmp₀ (𝒳 i) q p
Σ I 𝒳 .inv₀ {i ▸ x}{.i ▸ y} (refl ▸ p) = refl ▸ inv₀ (𝒳 i) p

_⊕_ : Setoid → Setoid → Setoid
𝒳 ⊕ 𝒴 = Σ (𝔽 2) (Vector.look (𝒳 ∷ 𝒴 ∷ []))

inl : ∀ {𝒳 𝒴} → Map 𝒳 (𝒳 ⊕ 𝒴)
inl .ap₀ x = zero ▸ x
inl .ap₁ f = refl ▸ f

inr : ∀ {𝒳 𝒴} → Map 𝒴 (𝒳 ⊕ 𝒴)
inr .ap₀ x = succ zero ▸ x
inr .ap₁ f = refl ▸ f

[_,_] : ∀ {𝒳 𝒴 𝒵} (F : Map 𝒳 𝒵) (G : Map 𝒴 𝒵) → Map (𝒳 ⊕ 𝒴) 𝒵
[ F , G ] .ap₀ (zero ▸ x) = ap₀ F x
[ F , G ] .ap₀ (succ zero ▸ y) = ap₀ G y
[ F , G ] .ap₀ (succ (succ ()) ▸ _)
[ F , G ] .ap₁ {zero ▸ x₀} {_ ▸ x₁} (refl ▸ f) = ap₁ F f
[ F , G ] .ap₁ {succ zero ▸ y₀} {_ ▸ y₁} (refl ▸ g) = ap₁ G g
[ F , G ] .ap₁ {succ (succ ()) ▸ _} p

[_⊕_] : ∀ {𝒳 𝒴 𝒞 𝒟} (F : Map 𝒳 𝒞) (G : Map 𝒴 𝒟) → Map (𝒳 ⊕ 𝒴) (𝒞 ⊕ 𝒟)
[ F ⊕ G ] = [ cmp inl F , cmp inr G ]
