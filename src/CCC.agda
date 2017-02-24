module CCC where

open import Basis
open import Cubical

module CCC where

infixr 1 _⇒_

open C
  using (Op)
  using (≪Functor≫)
  using (≪Presheaf≫)
  using (≪Setoid≫)
  using (≪_[-,_]≫)
  using (≪_∘-≫₁)

𝟘 : ∀ {I} → Presheaf I
𝟘 {I} .ap₀ x = S.𝟘
𝟘 {I} .ap₁ f = S.idn
𝟘 {I} .ap₂ α {()}
𝟘 {I} .coh-idn {x} {()}
𝟘 {I} .coh-cmp g f {()}

¡ : ∀ {I} {𝒳 : Presheaf I} → ≪Presheaf≫ I ⊧ 𝟘 ⇾ 𝒳
¡ {𝒳 = 𝒳} .ap₀ x = S.¡
¡ {𝒳 = 𝒳} .ap₁ f {()}

𝟙 : ∀ {I} → Presheaf I
𝟙 {I} .ap₀ x = S.𝟙
𝟙 {I} .ap₁ f = S.idn
𝟙 {I} .ap₂ α = *
𝟙 {I} .coh-idn = *
𝟙 {I} .coh-cmp g f = *

! : ∀ {I} {𝒳 : Presheaf I} → ≪Presheaf≫ I ⊧ 𝒳 ⇾ 𝟙
! {𝒳 = 𝒳} .ap₀ x = S.!
! {𝒳 = 𝒳} .ap₁ f = *

_⊗_ : ∀ {I} (𝒳 𝒴 : Presheaf I) → Presheaf I
(𝒳 ⊗ 𝒴) .ap₀ x = ap₀ 𝒳 x S.⊗ ap₀ 𝒴 x
(𝒳 ⊗ 𝒴) .ap₁ f = S.⟨ ap₁ 𝒳 f ⊗ ap₁ 𝒴 f ⟩
(𝒳 ⊗ 𝒴) .ap₂ α = ap₂ 𝒳 α , ap₂ 𝒴 α
(𝒳 ⊗ 𝒴) .coh-idn = coh-idn 𝒳 , coh-idn 𝒴
(𝒳 ⊗ 𝒴) .coh-cmp g f = coh-cmp 𝒳 g f , coh-cmp 𝒴 g f

fst : ∀ {I} {𝒳 𝒴 : Presheaf I} → ≪Presheaf≫ I ⊧ 𝒳 ⊗ 𝒴 ⇾ 𝒳
fst {I}{𝒳}{𝒴} .ap₀ x = S.fst
fst {I}{𝒳}{𝒴} .ap₁ f = idn₀ (ap₀ 𝒳 _)

snd : ∀ {I} {𝒳 𝒴 : Presheaf I} → ≪Presheaf≫ I ⊧ 𝒳 ⊗ 𝒴 ⇾ 𝒴
snd {I}{𝒳}{𝒴} .ap₀ x = S.snd
snd {I}{𝒳}{𝒴} .ap₁ f = idn₀ (ap₀ 𝒴 _)

⟨_,_⟩
  : ∀ {I} {𝒳 𝒴 𝒵 : Presheaf I}
  → (α : ≪Presheaf≫ I ⊧ 𝒵 ⇾ 𝒳)
  → (β : ≪Presheaf≫ I ⊧ 𝒵 ⇾ 𝒴)
  → ≪Presheaf≫ I ⊧ 𝒵 ⇾ 𝒳 ⊗ 𝒴
⟨ α , β ⟩ .ap₀ x = S.⟨ ap₀ α x , ap₀ β x ⟩
⟨ α , β ⟩ .ap₁ f = ap₁ α f , ap₁ β f

_⇒₀_
  : ∀ {I} (𝒳 𝒴 : Presheaf I)
  → ⟪ I ⟫ .●
  → Setoid
_⇒₀_ {I} 𝒳 𝒴 x = ≪hom≫ (≪Presheaf≫ I) (≪ I [-, x ]≫ ⊗ 𝒳) 𝒴

_⇒₁₀₀_
  : ∀ {I} (𝒳 𝒴 : Presheaf I) {y a x}
  → I ⊧ a ⇾ y
  → ≪Presheaf≫ I ⊧ ≪ I [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴
  → ≪Setoid≫ ⊧ ≪hom≫ I x a S.⊗ ap₀ 𝒳 x ⇾ ap₀ 𝒴 x
_⇒₁₀₀_ 𝒳 𝒴 {y}{a}{x} g α =
  S.cmp (ap₀ α x) S.⟨ ap₀ C.≪ g ∘-≫₁ x ⊗ S.idn ⟩

_⇒₁₀_
  : ∀ {I} (𝒳 𝒴 : Presheaf I) {y a}
  → I ⊧ a ⇾ y
  → ≪Presheaf≫ I ⊧ ≪ I [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴
  → ≪Presheaf≫ I ⊧ ≪ I [-, a ]≫ ⊗ 𝒳 ⇾ 𝒴
_⇒₁₀_ {I} 𝒳 𝒴 g α .ap₀ x = (𝒳 ⇒₁₀₀ 𝒴) g α
_⇒₁₀_ {I} 𝒳 𝒴 g α .ap₁ {a}{x} k =
  cmp₀ (ap₀ 𝒴 x)
    (ap₁ α k)
    (ap₁ (ap₀ α x) (inv₁ I (coh-α I) , idn₀ (ap₀ 𝒳 x)))

_⇒₁₁_
  : ∀ {I} (𝒳 𝒴 : Presheaf I) {y a} {g : ⟪ I ⟫ .∂ a y .●}
  → (α β : ≪Presheaf≫ I ⊧ ≪ I [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴)
  → hom ((𝒳 ⇒₀ 𝒴) y) α β
  → hom ((𝒳 ⇒₀ 𝒴) a) ((𝒳 ⇒₁₀ 𝒴) g α) ((𝒳 ⇒₁₀ 𝒴) g β)
_⇒₁₁_ 𝒳 𝒴 α β p = p

_⇒₁_
  : ∀ {I} (𝒳 𝒴 : Presheaf I) {x y}
  → I ⊧ y ⇾ x
  → ≪Setoid≫ ⊧ (𝒳 ⇒₀ 𝒴) x ⇾ (𝒳 ⇒₀ 𝒴) y
_⇒₁_ 𝒳 𝒴 f .ap₀ = (𝒳 ⇒₁₀ 𝒴) f
_⇒₁_ 𝒳 𝒴 f .ap₁ {α}{β} = (𝒳 ⇒₁₁ 𝒴) α β

_⇒₂_
  : ∀ {I} (𝒳 𝒴 : Presheaf I)
  → ∀ {y a}{g₀ g₁ : Op I ⊧ y ⇾ a}
  → Op I ⊧ g₀ ⇔ g₁
  → ≪Setoid≫ ⊧ (𝒳 ⇒₁ 𝒴) g₀ ⇔ (𝒳 ⇒₁ 𝒴) g₁
_⇒₂_ {I} 𝒳 𝒴 {y}{a}{g₀}{g₁} p {α}{x}{f , s} =
  ap₁ (ap₀ α x) (coh-ω-λ I p , idn₀ (ap₀ 𝒳 x))

_⇒_ : ∀ {I} (𝒳 𝒴 : Presheaf I) → Presheaf I
_⇒_ {I} 𝒳 𝒴 .ap₀ = 𝒳 ⇒₀ 𝒴
_⇒_ {I} 𝒳 𝒴 .ap₁ = 𝒳 ⇒₁ 𝒴
_⇒_ {I} 𝒳 𝒴 .ap₂ = 𝒳 ⇒₂ 𝒴
_⇒_ {I} 𝒳 𝒴 .coh-idn {y}{α}{x}{f , s} =
  ap₁ (ap₀ α x) (coh-λ I , idn₀ (ap₀ 𝒳 x))
_⇒_ {I} 𝒳 𝒴 .coh-cmp {y}{b}{a} g h {α}{x}{f , s} =
  ap₁ (ap₀ α x) (coh-α I , idn₀ (ap₀ 𝒳 x))

-- FIXME: clean this up
ƛ
  : ∀ {I} {Γ 𝒳 𝒴 : Presheaf I}
  → ≪Presheaf≫ I ⊧ Γ ⊗ 𝒳 ⇾ 𝒴
  → ≪Presheaf≫ I ⊧ Γ ⇾ 𝒳 ⇒ 𝒴
ƛ {I}{Γ} α .ap₀ j .ap₀ γ .ap₀ i .ap₀ (f , x) =
  ap₀ (ap₀ α i) (ap₀ (ap₁ Γ f) γ , x)
ƛ {I}{Γ} α .ap₀ j .ap₀ γ .ap₀ i .ap₁ {f₀ , x₀}{f₁ , x₁} (β , p) =
  ap₁ (ap₀ α i) (ap₂ Γ β {γ} , p)
ƛ {I}{Γ}{𝒳}{𝒴} α .ap₀ j .ap₀ γ .ap₁ {k}{i} f {g , x} =
  cmp₀ (ap₀ 𝒴 i)
    (ap₁ α f)
    (ap₁ (ap₀ α i) (coh-cmp Γ f g , idn₀ (ap₀ 𝒳 i)))
ƛ {I}{Γ}{𝒳}{𝒴} α .ap₀ i .ap₁ {γ₀}{γ₁} f {j}{g , x} =
  ap₁ (ap₀ α j) (ap₁ (ap₁ Γ g) f , idn₀ (ap₀ 𝒳 j))
ƛ {I}{Γ}{𝒳}{𝒴} α .ap₁ {j}{k} f {γ}{i}{g , x} =
  ap₁ (ap₀ α i)
    ( inv₀ (ap₀ Γ i) (coh-cmp Γ g f)
    , idn₀ (ap₀ 𝒳 i)
    )
