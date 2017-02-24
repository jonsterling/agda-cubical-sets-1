module CCC where

open import Basis
open import Cubical

module CCC where

𝟘 : ∀ {Γ} → Presheaf Γ
𝟘 {Γ} .ap₀ x = S.𝟘
𝟘 {Γ} .ap₁ f = S.idn
𝟘 {Γ} .ap₂ α {()}
𝟘 {Γ} .coh-idn {x} {()}
𝟘 {Γ} .coh-cmp g f {()}

¡ : ∀ {Γ} {𝒳 : Presheaf Γ} → Transform 𝟘 𝒳
¡ {𝒳 = 𝒳} .ap₀ x = S.¡
¡ {𝒳 = 𝒳} .ap₁ f {()}

𝟙 : ∀ {Γ} → Presheaf Γ
𝟙 {Γ} .ap₀ x = S.𝟙
𝟙 {Γ} .ap₁ f = S.idn
𝟙 {Γ} .ap₂ α = *
𝟙 {Γ} .coh-idn = *
𝟙 {Γ} .coh-cmp g f = *

! : ∀ {Γ} {𝒳 : Presheaf Γ} → Transform 𝒳 𝟙
! {𝒳 = 𝒳} .ap₀ x = S.!
! {𝒳 = 𝒳} .ap₁ f = *

_⊗_ : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) → Presheaf Γ
(𝒳 ⊗ 𝒴) .ap₀ x = ap₀ 𝒳 x S.⊗ ap₀ 𝒴 x
(𝒳 ⊗ 𝒴) .ap₁ f = S.⟨ ap₁ 𝒳 f ⊗ ap₁ 𝒴 f ⟩
(𝒳 ⊗ 𝒴) .ap₂ α = ap₂ 𝒳 α , ap₂ 𝒴 α
(𝒳 ⊗ 𝒴) .coh-idn = coh-idn 𝒳 , coh-idn 𝒴
(𝒳 ⊗ 𝒴) .coh-cmp g f = coh-cmp 𝒳 g f , coh-cmp 𝒴 g f

fst : ∀ {Γ} {𝒳 𝒴 : Presheaf Γ} → Transform (𝒳 ⊗ 𝒴) 𝒳
fst {Γ}{𝒳}{𝒴} .ap₀ x = S.fst
fst {Γ}{𝒳}{𝒴} .ap₁ f = idn₀ (ap₀ 𝒳 _)

snd : ∀ {Γ} {𝒳 𝒴 : Presheaf Γ} → Transform (𝒳 ⊗ 𝒴) 𝒴
snd {Γ}{𝒳}{𝒴} .ap₀ x = S.snd
snd {Γ}{𝒳}{𝒴} .ap₁ f = idn₀ (ap₀ 𝒴 _)

⟨_,_⟩
  : ∀ {Γ} {𝒳 𝒴 H : Presheaf Γ}
  → (α : Transform H 𝒳)
  → (β : Transform H 𝒴)
  → Transform H (𝒳 ⊗ 𝒴)
⟨ α , β ⟩ .ap₀ x = S.⟨ ap₀ α x , ap₀ β x ⟩
⟨ α , β ⟩ .ap₁ f = ap₁ α f , ap₁ β f

_⇒₀_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ)
  → ⟪ Γ ⟫ .●
  → Setoid
_⇒₀_ {Γ} 𝒳 𝒴 x = ≪hom≫ (C.≪Functor≫ (C.Op Γ) C.≪Setoid≫) (ap₀ (Yoneda Γ) x ⊗ 𝒳) 𝒴

_⇒₁₀_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) {y a}
  → Γ ⊧ a ⇾ y
  → C.≪Functor≫ _ _ ⊧ ap₀ (Yoneda Γ) y ⊗ 𝒳 ⇾ 𝒴
  → C.≪Functor≫ _ _ ⊧ ap₀ (Yoneda Γ) a ⊗ 𝒳 ⇾ 𝒴
_⇒₁₀_ {Γ} 𝒳 𝒴 {y}{a} g α .ap₀ x .ap₀ (f , s) = ap₀ (ap₀ α x) (cmp₀ Γ g f , s)
_⇒₁₀_ {Γ} 𝒳 𝒴 {y}{a} g α .ap₀ x .ap₁ {f₀ , s₀}{f₁ , s₁} (β , p) = ap₁ (ap₀ α x) (coh-ω-ρ Γ β , p)
_⇒₁₀_ {Γ} 𝒳 𝒴 {y}{b} g α .ap₁ {a}{x} k {f , s} =
  cmp₀ (ap₀ 𝒴 x)
    (ap₁ α k)
    (ap₁ (ap₀ α x) (inv₁ Γ (coh-α Γ) , idn₀ (ap₀ 𝒳 x)))

_⇒₁₁_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) {y a} (g : ⟪ Γ ⟫ .∂ a y .●) {α β}
  → hom ((𝒳 ⇒₀ 𝒴) y) α β
  → hom ((𝒳 ⇒₀ 𝒴) a) ((𝒳 ⇒₁₀ 𝒴) g α) ((𝒳 ⇒₁₀ 𝒴) g β)
_⇒₁₁_ {Γ} 𝒳 𝒴 {y}{a} g {α}{β} p {x} {f , s} = p

_⇒₁_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) {x y}
  → Γ ⊧ y ⇾ x
  → C.≪Setoid≫ ⊧ (𝒳 ⇒₀ 𝒴) x ⇾ (𝒳 ⇒₀ 𝒴) y
_⇒₁_ 𝒳 𝒴 f .ap₀ = (𝒳 ⇒₁₀ 𝒴) f
_⇒₁_ 𝒳 𝒴 f .ap₁ {α}{β} = (𝒳 ⇒₁₁ 𝒴) f {α}{β}

_⇒₂_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ)
  → ∀ {y a}{g₀ g₁ : C.Op Γ ⊧ y ⇾ a}
  → C.Op Γ ⊧ g₀ ⇔ g₁
  → C.≪Setoid≫ ⊧ (𝒳 ⇒₁ 𝒴) g₀ ⇔ (𝒳 ⇒₁ 𝒴) g₁
_⇒₂_ {Γ} 𝒳 𝒴 {y}{a}{g₀}{g₁} p {α}{x}{f , s} = ap₁ (ap₀ α x) (coh-ω-λ Γ p , idn₀ (ap₀ 𝒳 x))

_⇒_ : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) → Presheaf Γ
_⇒_ {Γ} 𝒳 𝒴 .ap₀ = 𝒳 ⇒₀ 𝒴
_⇒_ {Γ} 𝒳 𝒴 .ap₁ = 𝒳 ⇒₁ 𝒴
_⇒_ {Γ} 𝒳 𝒴 .ap₂ = 𝒳 ⇒₂ 𝒴
_⇒_ {Γ} 𝒳 𝒴 .coh-idn {y}{α}{x}{f , s} = ap₁ (ap₀ α x) (coh-λ Γ , idn₀ (ap₀ 𝒳 x))
_⇒_ {Γ} 𝒳 𝒴 .coh-cmp {y}{b}{a} g h {α}{x}{f , s} = ap₁ (ap₀ α x) (coh-α Γ , idn₀ (ap₀ 𝒳 x))
