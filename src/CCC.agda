module CCC where

open import Basis
open import Cubical

module CCC where

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

⟨_⊗_⟩
  : ∀ {I} {𝒳 𝒴 𝒞 𝒟 : Presheaf I}
  → (α : ≪Presheaf≫ I ⊧ 𝒳 ⇾ 𝒞)
  → (β : ≪Presheaf≫ I ⊧ 𝒴 ⇾ 𝒟)
  → ≪Presheaf≫ I ⊧ 𝒳 ⊗ 𝒴 ⇾ 𝒞 ⊗ 𝒟
⟨ α ⊗ β ⟩ = ⟨ cmp₀ (≪Presheaf≫ _) α fst , cmp₀ (≪Presheaf≫ _) β snd ⟩

module ⇒ {I} (𝒳 𝒴 : Presheaf I) where
  infixr 1 _⇒_

  exp₀ : ⟪ I ⟫ .● → Setoid
  exp₀ i = ≪hom≫ (≪Presheaf≫ I) (≪ I [-, i ]≫ ⊗ 𝒳) 𝒴

  exp₁₀₀
    : ∀ {y a x}
    → I ⊧ a ⇾ y
    → ≪Presheaf≫ I ⊧ ≪ I [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴
    → ≪Setoid≫ ⊧ ≪hom≫ I x a S.⊗ ap₀ 𝒳 x ⇾ ap₀ 𝒴 x
  exp₁₀₀ {y}{a}{x} g α =
    S.cmp (ap₀ α x) S.⟨ ap₀ C.≪ g ∘-≫₁ x ⊗ S.idn ⟩

  exp₁₀
    : ∀ {y a}
    → I ⊧ a ⇾ y
    → ≪Presheaf≫ I ⊧ ≪ I [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴
    → ≪Presheaf≫ I ⊧ ≪ I [-, a ]≫ ⊗ 𝒳 ⇾ 𝒴
  exp₁₀ g α .ap₀ x = exp₁₀₀ g α
  exp₁₀ g α .ap₁ k =
    cmp₀ (ap₀ 𝒴 _)
      (ap₁ α k)
      (ap₁ (ap₀ α _) (inv₁ I (coh-α I) , idn₀ (ap₀ 𝒳 _)))

  exp₁₁
    : ∀ {y a} {g : ⟪ I ⟫ .∂ a y .●}
    → (α β : ≪Presheaf≫ I ⊧ ≪ I [-, y ]≫ ⊗ 𝒳 ⇾ 𝒴)
    → hom (exp₀ y) α β
    → hom (exp₀ a) (exp₁₀ g α) (exp₁₀ g β)
  exp₁₁ α β p = p

  exp₁ : ∀ {x y} → I ⊧ y ⇾ x → ≪Setoid≫ ⊧ exp₀ x ⇾ exp₀ y
  exp₁ f .ap₀ = exp₁₀ f
  exp₁ f .ap₁ {α}{β} = exp₁₁ α β

  exp₂
    : ∀ {y a}{g₀ g₁ : Op I ⊧ y ⇾ a}
    → Op I ⊧ g₀ ⇔ g₁
    → ≪Setoid≫ ⊧ exp₁ g₀ ⇔ exp₁ g₁
  exp₂ {y}{a}{g₀}{g₁} p {α}{x}{f , s} =
    ap₁ (ap₀ α x) (coh-ω-λ I p , idn₀ (ap₀ 𝒳 x))

  _⇒_ : Presheaf I
  _⇒_ .ap₀ = exp₀
  _⇒_ .ap₁ = exp₁
  _⇒_ .ap₂ = exp₂
  _⇒_ .coh-idn {y} {α} = ap₁ (ap₀ α _) (coh-λ I , idn₀ (ap₀ 𝒳 _))
  _⇒_ .coh-cmp g h {α} = ap₁ (ap₀ α _) (coh-α I , idn₀ (ap₀ 𝒳 _))
open ⇒ public
  using (_⇒_)

module ƛ {I} {Γ 𝒳 𝒴 : Presheaf I} (α : ≪Presheaf≫ I ⊧ Γ ⊗ 𝒳 ⇾ 𝒴) where
  curry₀₀
    : ∀ {i} (γ : obj (ap₀ Γ i))
    → ≪Presheaf≫ I ⊧ (≪ I [-, i ]≫ ⊗ 𝒳) ⇾ 𝒴
  curry₀₀ γ = cmp₀ (≪Presheaf≫ _) α ⟨ ⊢yoneda ⊗ idn₀ (≪Presheaf≫ I) ⟩
    where ⊢yoneda = ap₀ (≅.from (C.⊢yoneda Γ)) γ

  curry₀₁
    : ∀ {i γ δ}
    → hom (ap₀ Γ i) γ δ
    → hom ((ap₀ (𝒳 ⇒ 𝒴) i)) (curry₀₀ γ) (curry₀₀ δ)
  curry₀₁ p = ap₁ (ap₀ α _) (ap₁ (ap₁ Γ _) p , idn₀ (ap₀ 𝒳 _))

  curry₀ : ∀ i → ≪Setoid≫ ⊧ ap₀ Γ i ⇾ ap₀ (𝒳 ⇒ 𝒴) i
  curry₀ i .ap₀ = curry₀₀
  curry₀ i .ap₁ = curry₀₁

  curry₁
    : ∀ {i j}
    → (f : Op I ⊧ i ⇾ j)
    → ≪Setoid≫
    ⊧  cmp₀ ≪Setoid≫ (curry₀ j) (ap₁ Γ f)
    ⇔ cmp₀ ≪Setoid≫ (ap₁ (𝒳 ⇒ 𝒴) f) (curry₀ i)
  curry₁ g {γ} = ap₁ (ap₀ α _) (inv₀ (ap₀ Γ _) (coh-cmp Γ _ g) , idn₀ (ap₀ 𝒳 _))

  ƛ : ≪Presheaf≫ I ⊧ Γ ⇾ 𝒳 ⇒ 𝒴
  ƛ .ap₀ = curry₀
  ƛ .ap₁ = curry₁
open ƛ public
  using (ƛ)
