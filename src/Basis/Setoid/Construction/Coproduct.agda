module Basis.Setoid.Construction.Coproduct where

open import Basis.Setoid.Map
open import Basis.Prelude

module _ where
  open import Basis.Setoid.Boot

  Σ : (I : Set) (𝒳 : I → Setoid) → Setoid
  Σ I 𝒳 .obj = T.Σ I λ i → obj (𝒳 i)
  Σ I 𝒳 .hom (i ▸ x) (j ▸ y) = T.Σ (i ≡ j) λ {refl → hom (𝒳 i) x y}
  Σ I 𝒳 .idn₀ {i ▸ x} = refl ▸ idn₀ (𝒳 i)
  Σ I 𝒳 .cmp₀ {i ▸ x}{.i ▸ y}{.i ▸ z} (refl ▸ q) (refl ▸ p) = refl ▸ cmp₀ (𝒳 i) q p
  Σ I 𝒳 .inv₀ {i ▸ x}{.i ▸ y} (refl ▸ p) = refl ▸ inv₀ (𝒳 i) p

module ⊕ where
  open import Basis.Setoid.Boot as S
    hiding (hom)

  data hom (𝒳 𝒴 : Setoid) : (x y : obj 𝒳 T.⊕ obj 𝒴) → Set where
    inl : ∀ {x₀ x₁} (p : S.hom 𝒳 x₀ x₁) → hom 𝒳 𝒴 (T.inl x₀) (T.inl x₁)
    inr : ∀ {y₀ y₁} (p : S.hom 𝒴 y₀ y₁) → hom 𝒳 𝒴 (T.inr y₀) (T.inr y₁)

open import Basis.Setoid.Boot

_⊕_ : Setoid → Setoid → Setoid
(𝒳 ⊕ 𝒴) .obj = obj 𝒳 T.⊕ obj 𝒴
(𝒳 ⊕ 𝒴) .hom = ⊕.hom 𝒳 𝒴
(𝒳 ⊕ 𝒴) .idn₀ {T.inl a} = ⊕.inl (idn₀ 𝒳)
(𝒳 ⊕ 𝒴) .idn₀ {T.inr b} = ⊕.inr (idn₀ 𝒴)
(𝒳 ⊕ 𝒴) .cmp₀ (⊕.inl q) (⊕.inl p) = ⊕.inl (cmp₀ 𝒳 q p)
(𝒳 ⊕ 𝒴) .cmp₀ (⊕.inr q) (⊕.inr p) = ⊕.inr (cmp₀ 𝒴 q p)
(𝒳 ⊕ 𝒴) .inv₀ (⊕.inl p) = ⊕.inl (inv₀ 𝒳 p)
(𝒳 ⊕ 𝒴) .inv₀ (⊕.inr p) = ⊕.inr (inv₀ 𝒴 p)

inl : ∀ {𝒳 𝒴} → Map 𝒳 (𝒳 ⊕ 𝒴)
inl .ap₀ = T.inl
inl .ap₁ = ⊕.inl

inr : ∀ {𝒳 𝒴} → Map 𝒴 (𝒳 ⊕ 𝒴)
inr .ap₀ = T.inr
inr .ap₁ = ⊕.inr

[_,_] : ∀ {𝒳 𝒴 𝒵} (F : Map 𝒳 𝒵) (G : Map 𝒴 𝒵) → Map (𝒳 ⊕ 𝒴) 𝒵
[ F , G ] .ap₀ = T.[ ap₀ F , ap₀ G ]
[ F , G ] .ap₁ (⊕.inl p) = ap₁ F p
[ F , G ] .ap₁ (⊕.inr q) = ap₁ G q

[_⊕_] : ∀ {𝒳 𝒴 𝒞 𝒟} (F : Map 𝒳 𝒞) (G : Map 𝒴 𝒟) → Map (𝒳 ⊕ 𝒴) (𝒞 ⊕ 𝒟)
[ F ⊕ G ] = [ cmp inl F , cmp inr G ]
