module CCC where

open import Basis
open import Cubical

module CCC where

𝟘 : ∀ {𝒳} → Presheaf 𝒳
𝟘 {𝒳} .ap₀ x = S.𝟘
𝟘 {𝒳} .ap₁ f = S.idn
𝟘 {𝒳} .ap₂ α {()}
𝟘 {𝒳} .coh-idn {x} {()}
𝟘 {𝒳} .coh-cmp g f {()}

𝟙 : ∀ {𝒳} → Presheaf 𝒳
𝟙 {𝒳} .ap₀ x = S.𝟙
𝟙 {𝒳} .ap₁ f = S.idn
𝟙 {𝒳} .ap₂ α = *
𝟙 {𝒳} .coh-idn = *
𝟙 {𝒳} .coh-cmp g f = *

_⊗_ : ∀ {𝒳} (F G : Presheaf 𝒳) → Presheaf 𝒳
(F ⊗ G) .ap₀ x = ap₀ F x S.⊗ ap₀ G x
(F ⊗ G) .ap₁ {x}{y} f .ap₀ (F·x , G·x) = ap₀ (ap₁ F f) F·x , ap₀ (ap₁ G f) G·x
(F ⊗ G) .ap₁ {x}{y} f .ap₁ {F·x , G·x}{F·y , G·y} (p , q) = ap₁ (ap₁ F f) p , ap₁ (ap₁ G f) q
(F ⊗ G) .ap₂ {x}{y}{f}{g} α {F·x , G·x} = ap₂ F α , ap₂ G α
(F ⊗ G) .coh-idn {x}{F·x , G·x} = coh-idn F , coh-idn G
(F ⊗ G) .coh-cmp g f = coh-cmp F g f , coh-cmp G g f

fst : ∀ {𝒳} {F G : Presheaf 𝒳} → Transform (F ⊗ G) F
fst {𝒳}{F}{G} .ap₀ x .ap₀ = T.fst
fst {𝒳}{F}{G} .ap₀ x .ap₁ = T.fst
fst {𝒳}{F}{G} .ap₁ {x}{y} f = idn₀ (ap₀ F y)

snd : ∀ {𝒳} {F G : Presheaf 𝒳} → Transform (F ⊗ G) G
snd {𝒳}{F}{G} .ap₀ x .ap₀ = T.snd
snd {𝒳}{F}{G} .ap₀ x .ap₁ = T.snd
snd {𝒳}{F}{G} .ap₁ {x}{y} f = idn₀ (ap₀ G y)

⟨_,_⟩
  : ∀ {𝒳} {F G H : Presheaf 𝒳}
  → (α : Transform H F)
  → (β : Transform H G)
  → Transform H (F ⊗ G)
⟨ α , β ⟩ .ap₀ x .ap₀ = T.⟨ ap₀ (ap₀ α x) , ap₀ (ap₀ β x) ⟩
⟨ α , β ⟩ .ap₀ x .ap₁ = T.⟨ ap₁ (ap₀ α x) , ap₁ (ap₀ β x) ⟩
⟨ α , β ⟩ .ap₁ f = ap₁ α f , ap₁ β f

_⊸_ : ∀ {𝒳} (F G : Presheaf 𝒳) → Presheaf 𝒳
_⊸_ {𝒳} F G .ap₀ x = ≪hom≫ (C.≪Functor≫ (C.Op 𝒳) C.≪Setoid≫) (ap₀ (Yoneda 𝒳) x ⊗ F) G
_⊸_ {𝒳} F G .ap₁ {y}{a} g .ap₀ α .ap₀ x .ap₀ (f , s) = ap₀ (ap₀ α x) (cmp₀ 𝒳 g f , s)
_⊸_ {𝒳} F G .ap₁ {y}{a} g .ap₀ α .ap₀ x .ap₁ {p₀ , s₀}{p₁ , s₁} (π , σ) = ap₁ (ap₀ α x) (coh-ω-ρ 𝒳 π , σ)
_⊸_ {𝒳} F G .ap₁ {y}{a} g .ap₀ α .ap₁ {x₀}{x₁} f {c , v} =
  cmp₀ (ap₀ G x₁)
    (ap₁ α f)
    (ap₁ (ap₀ α x₁)
      ( cmp₁ 𝒳
          (coh-ω-λ 𝒳
            (cmp₁ 𝒳
              (cmp₁ 𝒳
                (cmp₁ 𝒳
                  (coh-α 𝒳)
                  (coh-ω-λ 𝒳 (inv₁ 𝒳 (coh-λ 𝒳))))
                (coh-ω-λ 𝒳 (coh-ρ 𝒳)))
              (inv₁ 𝒳 (coh-α 𝒳))))
          (inv₁ 𝒳 (coh-α 𝒳))
      , idn₀ (ap₀ F x₁)))
_⊸_ {𝒳} F G .ap₁ {y}{a} g .ap₁ {α}{β} k {x} {f , s} = k
_⊸_ {𝒳} F G .ap₂ {y}{a}{g₀}{g₁} p {α}{x}{f , s} = ap₁ (ap₀ α x) (coh-ω-λ 𝒳 p , idn₀ (ap₀ F x))
_⊸_ {𝒳} F G .coh-idn {y}{α}{x}{f , s} = ap₁ (ap₀ α x) (coh-λ 𝒳 , idn₀ (ap₀ F x))
_⊸_ {𝒳} F G .coh-cmp g h {α}{x}{f , s} = ap₁ (ap₀ α x) (coh-α 𝒳 , idn₀ (ap₀ F x))
