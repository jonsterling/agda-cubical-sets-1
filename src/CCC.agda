module CCC where

open import Basis
open import Cubical

module CCC where

open C
  using (Op)
  using (≪Functor≫)
  using (≪Setoid≫)
  using (≪_[-,_]≫)
  using (≪_∘-≫₁)

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
_⇒₀_ {Γ} 𝒳 𝒴 x = ≪hom≫ (≪Functor≫ (Op Γ) ≪Setoid≫) (≪ Γ [-, x ]≫ ⊗ 𝒳) 𝒴

_⇒₁₀₀_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) {y a x}
  → Γ ⊧ a ⇾ y
  → ≪Functor≫ _ _ ⊧ ≪ Γ [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴
  → ≪Setoid≫ ⊧ ≪hom≫ Γ x a S.⊗ ap₀ 𝒳 x ⇾ ap₀ 𝒴 x
_⇒₁₀₀_ 𝒳 𝒴 {y}{a}{x} g α = S.cmp (ap₀ α x) S.⟨ ap₀ C.≪ g ∘-≫₁ x ⊗ S.idn ⟩

_⇒₁₀_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) {y a}
  → Γ ⊧ a ⇾ y
  → ≪Functor≫ _ _ ⊧ ≪ Γ [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴
  → ≪Functor≫ _ _ ⊧ ≪ Γ [-, a ]≫ ⊗ 𝒳 ⇾ 𝒴
_⇒₁₀_ {Γ} 𝒳 𝒴 g α .ap₀ x = (𝒳 ⇒₁₀₀ 𝒴) g α
_⇒₁₀_ {Γ} 𝒳 𝒴 g α .ap₁ {a}{x} k =
  cmp₀ (ap₀ 𝒴 x)
    (ap₁ α k)
    (ap₁ (ap₀ α x) (inv₁ Γ (coh-α Γ) , idn₀ (ap₀ 𝒳 x)))

_⇒₁₁_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) {y a} {g : ⟪ Γ ⟫ .∂ a y .●}
  → (α β : ≪Functor≫ _ _ ⊧ ≪ Γ [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴)
  → hom ((𝒳 ⇒₀ 𝒴) y) α β
  → hom ((𝒳 ⇒₀ 𝒴) a) ((𝒳 ⇒₁₀ 𝒴) g α) ((𝒳 ⇒₁₀ 𝒴) g β)
_⇒₁₁_ 𝒳 𝒴 α β p = p

_⇒₁_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) {x y}
  → Γ ⊧ y ⇾ x
  → ≪Setoid≫ ⊧ (𝒳 ⇒₀ 𝒴) x ⇾ (𝒳 ⇒₀ 𝒴) y
_⇒₁_ 𝒳 𝒴 f .ap₀ = (𝒳 ⇒₁₀ 𝒴) f
_⇒₁_ 𝒳 𝒴 f .ap₁ {α}{β} = (𝒳 ⇒₁₁ 𝒴) α β

_⇒₂_
  : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ)
  → ∀ {y a}{g₀ g₁ : Op Γ ⊧ y ⇾ a}
  → Op Γ ⊧ g₀ ⇔ g₁
  → ≪Setoid≫ ⊧ (𝒳 ⇒₁ 𝒴) g₀ ⇔ (𝒳 ⇒₁ 𝒴) g₁
_⇒₂_ {Γ} 𝒳 𝒴 {y}{a}{g₀}{g₁} p {α}{x}{f , s} = ap₁ (ap₀ α x) (coh-ω-λ Γ p , idn₀ (ap₀ 𝒳 x))

_⇒_ : ∀ {Γ} (𝒳 𝒴 : Presheaf Γ) → Presheaf Γ
_⇒_ {Γ} 𝒳 𝒴 .ap₀ = 𝒳 ⇒₀ 𝒴
_⇒_ {Γ} 𝒳 𝒴 .ap₁ = 𝒳 ⇒₁ 𝒴
_⇒_ {Γ} 𝒳 𝒴 .ap₂ = 𝒳 ⇒₂ 𝒴
_⇒_ {Γ} 𝒳 𝒴 .coh-idn {y}{α}{x}{f , s} = ap₁ (ap₀ α x) (coh-λ Γ , idn₀ (ap₀ 𝒳 x))
_⇒_ {Γ} 𝒳 𝒴 .coh-cmp {y}{b}{a} g h {α}{x}{f , s} = ap₁ (ap₀ α x) (coh-α Γ , idn₀ (ap₀ 𝒳 x))
