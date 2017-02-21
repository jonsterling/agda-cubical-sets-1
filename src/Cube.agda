{-# OPTIONS --type-in-type #-}

module Cube where

open import Category
open import DeMorgan as 𝕀
  hiding (_≅_)
  hiding (idn)
open import Globular
open import Prelude
  hiding (¬_)
open import Setoid
  hiding (module Setoid)
  using (Setoid)
open import Symbol

infix  6 _≔_
infixl 1 _≫=_
infixr 1 _≫=≫_

record Decl (Γ : Symbols) : Set where
  constructor _≔_
  field
    ▸i : String
    ▸φ : 𝕀 Γ
open Decl public

data Sub (Δ : Symbols) : (Γ : Symbols) → Set where
  []
    : Sub Δ []
  _∷_
    : ∀ {Γ}
    → (δ : Decl Δ)
    → (f : Sub Δ Γ)
    → Sub Δ (▸i δ ∷ Γ)
  loop
    : Sub Δ Δ
  _≫=≫_
    : ∀ {Γ Θ}
    → (f : Sub Θ Γ)
    → (g : Sub Δ Θ)
    → Sub Δ Γ

mutual
  look : ∀ {Γ Δ} → Sub Δ Γ → Name Γ → 𝕀 Δ
  look [] (pt _ ())
  look (_ ≔ φ ∷ _) (pt _ (stop)) = φ
  look (_ ∷ f) (pt i (step _ _ ε)) = look f (pt i ε)
  look (loop) ε = var ε
  look (f ≫=≫ g) ε = look f ε ≫= g

  _≫=_ : ∀ {Γ Δ} → 𝕀 Γ → Sub Δ Γ → 𝕀 Δ
  var i ≫= f = look f i
  #0 ≫= f = #0
  #1 ≫= f = #1
  a ∨ b ≫= f = (a ≫= f) ∨ (b ≫= f)
  a ∧ b ≫= f = (a ≫= f) ∧ (b ≫= f)
  ¬ a ≫= f = ¬ (a ≫= f)

_≅_ : ∀ {Δ Γ} (f g : Sub Δ Γ) → Set
_≅_ f g = ∀ {i} → look f i 𝕀.≅ look g i

idn
  : ∀ {Γ} {a : 𝕀 Γ}
  → (a ≫= loop) ≡ a
idn {a = var _} = refl
idn {a = #0} = refl
idn {a = #1} = refl
idn {a = a ∨ b} = ≡.ap² _∨_ idn idn
idn {a = a ∧ b} = ≡.ap² _∧_ idn idn
idn {a = ¬ a} = ≡.ap ¬_ idn

rsp-lhs
  : ∀ {Γ Δ a b}
  → (f : Sub Δ Γ)
  → a 𝕀.≅ b
  → a ≫= f 𝕀.≅ b ≫= f
rsp-lhs f (𝕀.idn refl) = 𝕀.idn refl
rsp-lhs f (𝕀.cmp q p) = 𝕀.cmp (rsp-lhs f q) (rsp-lhs f p)
rsp-lhs f (𝕀.inv p) = 𝕀.inv (rsp-lhs f p)
rsp-lhs f 𝕀.∨-abs = 𝕀.∨-abs
rsp-lhs f 𝕀.∨-ass = 𝕀.∨-ass
rsp-lhs f 𝕀.∨-com = 𝕀.∨-com
rsp-lhs f 𝕀.∨-dis = 𝕀.∨-dis
rsp-lhs f 𝕀.∨-ide = 𝕀.∨-ide
rsp-lhs f (𝕀.∨-rsp p q) = 𝕀.∨-rsp (rsp-lhs f p) (rsp-lhs f q)
rsp-lhs f 𝕀.∨-uni = 𝕀.∨-uni
rsp-lhs f 𝕀.∧-abs = 𝕀.∧-abs
rsp-lhs f 𝕀.∧-ass = 𝕀.∧-ass
rsp-lhs f 𝕀.∧-com = 𝕀.∧-com
rsp-lhs f 𝕀.∧-dis = 𝕀.∧-dis
rsp-lhs f 𝕀.∧-ide = 𝕀.∧-ide
rsp-lhs f (𝕀.∧-rsp p q) = 𝕀.∧-rsp (rsp-lhs f p) (rsp-lhs f q)
rsp-lhs f 𝕀.∧-uni = 𝕀.∧-uni
rsp-lhs f 𝕀.¬-dis-∧ = 𝕀.¬-dis-∧
rsp-lhs f 𝕀.¬-dis-∨ = 𝕀.¬-dis-∨
rsp-lhs f 𝕀.¬-inv = 𝕀.¬-inv
rsp-lhs f (𝕀.¬-rsp p) = 𝕀.¬-rsp (rsp-lhs f p)
rsp-lhs f 𝕀.¬-#0 = 𝕀.¬-#0
rsp-lhs f 𝕀.¬-#1 = 𝕀.¬-#1

rsp-rhs
  : ∀ {Γ Δ} a
  → (f g : Sub Δ Γ)
  → f ≅ g
  → a ≫= f 𝕀.≅ a ≫= g
rsp-rhs (var i) f g α = α
rsp-rhs #0 f g α = 𝕀.idn refl
rsp-rhs #1 f g α = 𝕀.idn refl
rsp-rhs (a ∨ b) f g α = 𝕀.∨-rsp (rsp-rhs a f g α) (rsp-rhs b f g α)
rsp-rhs (a ∧ b) f g α = 𝕀.∧-rsp (rsp-rhs a f g α) (rsp-rhs b f g α)
rsp-rhs (¬ a) f g α = 𝕀.¬-rsp (rsp-rhs a f g α)

ass
  : ∀ {Γ Δ Θ}
  → (a : 𝕀 Γ)
  → (f : Sub Δ Γ)
  → (g : Sub Θ Δ)
  → (a ≫= (f ≫=≫ g)) ≡ ((a ≫= f) ≫= g)
ass (var _) f g = refl
ass #0 f g = refl
ass #1 f g = refl
ass (a ∨ b) f g = ≡.ap² _∨_ (ass a f g) (ass b f g)
ass (a ∧ b) f g = ≡.ap² _∧_ (ass a f g) (ass b f g)
ass (¬ a) f g = ≡.ap ¬_ (ass a f g)

rsp
  : ∀ {Γ Δ} a b
  → (f g : Sub Δ Γ)
  → a 𝕀.≅ b
  → f ≅ g
  → a ≫= f 𝕀.≅ b ≫= g
rsp a b f g α β = 𝕀.cmp (rsp-rhs b f g β) (rsp-lhs f α)

module _ where
  open import Setoid
    hiding (module Setoid)
    using (Setoid)

  -- the setoid of nominal cubes
  set : Symbols → Symbols → Setoid
  set Δ Γ .Setoid.obj = Sub Δ Γ
  set Δ Γ .Setoid.hom = _≅_
  set Δ Γ .Setoid.idn = 𝕀.idn refl
  set Δ Γ .Setoid.cmp β α {i} = 𝕀.cmp (β {i}) (α {i})
  set Δ Γ .Setoid.inv α {i} = 𝕀.inv (α {i})

-- the category of nominal cubes
cat : Category
⟪ cat ⟫ .● = Symbols
⟪ cat ⟫ .∂ Γ Δ .● = Sub Γ Δ
⟪ cat ⟫ .∂ Γ Δ .∂ f g .● = f ≅ g
⟪ cat ⟫ .∂ Γ Δ .∂ f g .∂ α β = Void
cat .idn₀ = loop
cat .cmp₀ = _≫=≫_
cat .idn₁ = 𝕀.idn refl
cat .cmp₁ β α {i} = 𝕀.cmp (β {i}) (α {i})
cat .inv₁ α {i} = 𝕀.inv (α {i})
cat .cmp₀* {f₀ = f₀}{f₁}{g₀}{g₁} β α {i} = rsp (look g₀ i) (look g₁ i) f₀ f₁ (β {i}) α
cat .coh-λ = 𝕀.idn refl
cat .coh-ρ = 𝕀.idn idn
cat .coh-α {f = f}{g}{h}{i} = 𝕀.idn (≡.inv (ass (look h i) g f))
