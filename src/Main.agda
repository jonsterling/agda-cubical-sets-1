{-# OPTIONS --type-in-type #-}

module Main where

open import Category
open import Globular
open import Prelude
  hiding (¬_)
open import Setoid
  hiding (module Setoid)
  using (Setoid)

module Symbols where
  infix  1 _∈_

  Symbols : Set
  Symbols = List String

  mutual
    data _∈_ (x : String) : Symbols → Set where
      stop
        : ∀ {xs}
        → x ∈ x ∷ xs
      step
        : ∀ {xs} y
        → (φ : x ≢ y) -- only allow refs to the first occurrence of x (shadowing)
        → (ε : x ∈ xs)
        → x ∈ y ∷ xs

    _≢_ : String → String → Set
    x ≢ y with x String.≟ y
    … | no  _ = T.𝟙
    … | yes _ = T.𝟘

  record Name (X : Symbols) : Set where
    constructor pt
    field
      x : String
      el : x ∈ X
  open Name public
open Symbols public

module 𝕀 where
  infix  0 _≅_
  infix  4 ¬_
  infixr 2 _∨_
  infixr 3 _∧_

  data 𝕀 (Γ : Symbols) : Set where
    var : (i : Name Γ) → 𝕀 Γ
    #0 : 𝕀 Γ
    #1 : 𝕀 Γ
    _∨_ : (a b : 𝕀 Γ) → 𝕀 Γ
    _∧_ : (a b : 𝕀 Γ) → 𝕀 Γ
    ¬_ : (a : 𝕀 Γ) → 𝕀 Γ

  instance
    ∈-stop : ∀ {Γ} (x : String) → x ∈ x ∷ Γ
    ∈-stop x = stop

    ∈-step : ∀ {y Γ} → (x : String) ⦃ ε : x ∈ Γ ⦄ ⦃ p : x ≢ y ⦄ → x ∈ y ∷ Γ
    ∈-step {y} x ⦃ ε ⦄ ⦃ p ⦄ = step y p ε

    ≪_≫ : ∀ {Γ} (x : String) ⦃ ε : x ∈ Γ ⦄ → 𝕀 Γ
    ≪ x ≫ ⦃ ε ⦄ = var (pt x ε)

  data _≅_ {Γ} : (a b : 𝕀 Γ) → Set where
    idn -- identity
      : ∀ {a b}
      → a ≡ b
      → a ≅ b
    cmp
      : ∀ {a b c}
      → (q : b ≅ c)
      → (p : a ≅ b)
      → a ≅ c
    inv -- symmetry
      : ∀ {a b}
      → (p : a ≅ b)
      → b ≅ a
    ∨-abs -- absorption
      : ∀ {a b}
      → a ∨ a ∧ b ≅ a
    ∨-ass -- associativity
      : ∀ {a b c}
      → a ∨ (b ∨ c) ≅ (a ∨ b) ∨ c
    ∨-com -- commutativity
      : ∀ {a b}
      → a ∨ b ≅ b ∨ a
    ∨-dis -- distributivity
      : ∀ {a b c}
      → a ∨ b ∧ c ≅ (a ∨ b) ∧ (a ∨ c)
    ∨-ide -- idempotency
      : ∀ {a}
      → a ∨ a ≅ a
    ∨-rsp -- congruence
      : ∀ {a₀ a₁ b₀ b₁}
      → a₀ ≅ a₁
      → b₀ ≅ b₁
      → a₀ ∨ b₀ ≅ a₁ ∨ b₁
    ∨-uni
      : ∀ {a}
      → a ∨ #0 ≅ a
    ∧-abs
      : ∀ {a b}
      → a ∧ (a ∨ b) ≅ a
    ∧-ass
      : ∀ {a b c}
      → a ∧ (b ∧ c) ≅ (a ∧ b) ∧ c
    ∧-com
      : ∀ {a b}
      → a ∧ b ≅ b ∧ a
    ∧-dis
      : ∀ {a b c}
      → a ∧ (b ∨ c) ≅ a ∧ b ∨ a ∧ c
    ∧-ide
      : ∀ {a}
      → a ∧ a ≅ a
    ∧-rsp
      : ∀ {a₀ a₁ b₀ b₁}
      → a₀ ≅ a₁
      → b₀ ≅ b₁
      → a₀ ∧ b₀ ≅ a₁ ∧ b₁
    ∧-uni
      : ∀ {a}
      → a ∧ #1 ≅ a
    ¬-dis-∧
      : ∀ {a b}
      → ¬ (a ∧ b) ≅ ¬ a ∨ ¬ b
    ¬-dis-∨
      : ∀ {a b}
      → ¬ (a ∨ b) ≅ ¬ a ∧ ¬ b
    ¬-inv
      : ∀ {a}
      → ¬ ¬ a ≅ a
    ¬-rsp
      : ∀ {a₀ a₁}
      → a₀ ≅ a₁
      → ¬ a₀ ≅ ¬ a₁
    ¬-#0
      : ¬ #0 ≅ #1
    ¬-#1
      : ¬ #1 ≅ #0

  postulate
    distinct : ∀ {Γ} → T.¬ _≅_ {Γ} #0 #1
open 𝕀 public
  hiding (module 𝕀)
  using (#0)
  using (#1)
  using (_∧_)
  using (_∨_)
  using (var)
  using (¬_)
  using (≪_≫)
  using (𝕀)

module Cube where
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
open Cube
  hiding (module Sub)
  using (Sub)
  using ([])
  using (_∷_)
  using (_≔_)
  using (_≫=_)
  using (_≫=≫_)
  using (look)
  using (loop)

module Presheaf where
  open import Setoid
    hiding (module Setoid)

  □Set : Set
  □Set = Presheaf Cube.cat

  ≪□Set≫ : Category
  ≪□Set≫ = ≪Presheaf≫ Cube.cat

  -- the formal or representable cube
  □ : Symbols → □Set
  □ = ap₀ (Yoneda Cube.cat)

  data Interval (I : Symbols) : Set where
    west : Interval I
    east : Interval I
    walk : (φ : 𝕀 I) → Interval I

  interval : □Set
  interval .ap₀ I .obj = Interval I
  interval .ap₀ I .hom east east = T.𝟙
  interval .ap₀ I .hom east (walk φ₁) = #1 𝕀.≅ φ₁
  interval .ap₀ I .hom (walk φ₀) east = φ₀ 𝕀.≅ #1
  interval .ap₀ I .hom (walk φ₀) (walk φ₁) = φ₀ 𝕀.≅ φ₁
  interval .ap₀ I .hom (walk φ₀) west = φ₀ 𝕀.≅ #0
  interval .ap₀ I .hom west (walk φ₁) = #0 𝕀.≅ φ₁
  interval .ap₀ I .hom west west = T.𝟙
  interval .ap₀ I .hom _ _ = T.𝟘
  interval .ap₀ I .idn {west} = *
  interval .ap₀ I .idn {east} = *
  interval .ap₀ I .idn {walk φ} = 𝕀.idn refl
  interval .ap₀ I .cmp {west} {west} {west} * * = *
  interval .ap₀ I .cmp {west} {west} {east} () *
  interval .ap₀ I .cmp {west} {west} {walk φ₂} q * = q
  interval .ap₀ I .cmp {west} {east} {west} () ()
  interval .ap₀ I .cmp {west} {east} {east} * ()
  interval .ap₀ I .cmp {west} {east} {walk φ₂} q ()
  interval .ap₀ I .cmp {west} {walk φ₁} {west} q p = *
  interval .ap₀ I .cmp {west} {walk φ₁} {east} q p = 𝕀.distinct (𝕀.cmp q p)
  interval .ap₀ I .cmp {west} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp {east} {west} {west} * ()
  interval .ap₀ I .cmp {east} {west} {east} () ()
  interval .ap₀ I .cmp {east} {west} {walk φ₂} q ()
  interval .ap₀ I .cmp {east} {east} {west} () *
  interval .ap₀ I .cmp {east} {east} {east} * * = *
  interval .ap₀ I .cmp {east} {east} {walk φ₂} q * = q
  interval .ap₀ I .cmp {east} {walk φ₁} {west} q p = 𝕀.distinct (𝕀.cmp (𝕀.inv p) (𝕀.inv q))
  interval .ap₀ I .cmp {east} {walk φ₁} {east} q p = *
  interval .ap₀ I .cmp {east} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp {walk φ₀} {west} {west} * p = p
  interval .ap₀ I .cmp {walk φ₀} {west} {east} () p
  interval .ap₀ I .cmp {walk φ₀} {west} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp {walk φ₀} {east} {west} () p
  interval .ap₀ I .cmp {walk φ₀} {east} {east} * p = p
  interval .ap₀ I .cmp {walk φ₀} {east} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp {walk φ₀} {walk φ₁} {west} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp {walk φ₀} {walk φ₁} {east} q p = 𝕀.cmp q p
  interval .ap₀ I .cmp {walk φ₀} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .ap₀ I .inv {west} {west} * = *
  interval .ap₀ I .inv {west} {east} ()
  interval .ap₀ I .inv {west} {walk φ₁} p = 𝕀.inv p
  interval .ap₀ I .inv {east} {west} ()
  interval .ap₀ I .inv {east} {east} * = *
  interval .ap₀ I .inv {east} {walk φ₁} p = 𝕀.inv p
  interval .ap₀ I .inv {walk φ₀} {west} p = 𝕀.inv p
  interval .ap₀ I .inv {walk φ₀} {east} p = 𝕀.inv p
  interval .ap₀ I .inv {walk φ₀} {walk φ₁} p = 𝕀.inv p
  interval .ap₁ f .ap₀ west = west
  interval .ap₁ f .ap₀ east = east
  interval .ap₁ f .ap₀ (walk φ) = walk (φ ≫= f)
  interval .ap₁ f .ap₁ {west} {west} * = *
  interval .ap₁ f .ap₁ {west} {east} ()
  interval .ap₁ f .ap₁ {west} {walk φ₁} p = Cube.rsp-lhs f p
  interval .ap₁ f .ap₁ {east} {west} ()
  interval .ap₁ f .ap₁ {east} {east} * = *
  interval .ap₁ f .ap₁ {east} {walk φ₁} p = Cube.rsp-lhs f p
  interval .ap₁ f .ap₁ {walk φ₀} {west} p = Cube.rsp-lhs f p
  interval .ap₁ f .ap₁ {walk φ₀} {east} p = Cube.rsp-lhs f p
  interval .ap₁ f .ap₁ {walk φ₀} {walk φ₁} p = Cube.rsp-lhs f p
  interval .ap₂ α {west} = *
  interval .ap₂ α {east} = *
  interval .ap₂ {Γ}{Δ}{f}{g} α {walk φ} = Cube.rsp-rhs φ f g α
  interval .coh-idn {Γ} {west} = *
  interval .coh-idn {Γ} {east} = *
  interval .coh-idn {Γ} {walk φ} = 𝕀.idn Cube.idn
  interval .coh-cmp {x₁} {y} {z} g f {west} = *
  interval .coh-cmp {x₁} {y} {z} g f {east} = *
  interval .coh-cmp {x₁} {y} {z} g f {walk φ} = 𝕀.idn (Cube.ass φ f g)

module Flattened where
  record □Set : Set where
    field -- setoids fibered over cubes
      obj
        : (Γ : Symbols)
        → Set
      hom
        : ∀ Γ
        → obj Γ → obj Γ → Set
      idn
        : ∀ {Γ x}
        → hom Γ x x
      cmp
        : ∀ {Γ x y z}
        → (q : hom Γ y z)
        → (p : hom Γ x y)
        → hom Γ x z
      inv
        : ∀ {Γ x y}
        → (p : hom Γ x y)
        → hom Γ y x
    field -- substitution across fibers
      sub
        : ∀ {Γ Δ}
        → (f : Sub Δ Γ)
        → obj Γ → obj Δ
      sub-idn
        : ∀ {Γ x}
        → hom Γ (sub loop x) x
      sub-cmp
        : ∀ {Γ Δ Θ x}
        → (g : Sub Θ Δ)
        → (f : Sub Δ Γ)
        → hom Θ (sub (f ≫=≫ g) x) (sub g (sub f x))
      sub-rsp -- functoriality or whiskering
        : ∀ {Γ Δ x y}
        → (f g : Sub Δ Γ)
        → (α : f Cube.≅ g)
        → (β : hom Γ x y)
        → hom Δ (sub f x) (sub g y)
  open □Set public

  record □Map (𝒳 𝒴 : □Set) : Set where
    no-eta-equality
    field
      ap₀ : ∀ {Γ} → obj 𝒳 Γ → obj 𝒴 Γ
      ap₁ : ∀ {Γ x y} → hom 𝒳 Γ x y → hom 𝒴 Γ (ap₀ x) (ap₀ y)
      ap₂ : ∀ {Γ Δ} (f : Sub Δ Γ) {x} → hom 𝒴 Δ (ap₀ (sub 𝒳 f x)) (sub 𝒴 f (ap₀ x))
  open □Map public
  {-# DISPLAY □Map.ap₀ 𝒳 x = 𝒳 x #-}
  {-# DISPLAY □Map.ap₁ 𝒳 p = 𝒳 p #-}
  {-# DISPLAY □Map.ap₂ 𝒳 f = 𝒳 f #-}

  ≪□Set≫ : Category
  ⟪ ≪□Set≫ ⟫ .● = □Set
  ⟪ ≪□Set≫ ⟫ .∂ 𝒳 𝒴 .● = □Map 𝒳 𝒴
  ⟪ ≪□Set≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .● = ∀ {Γ x} → hom 𝒴 Γ (ap₀ F x) (ap₀ G x)
  ⟪ ≪□Set≫ ⟫ .∂ 𝒳 𝒴 .∂ F G .∂ α β = Void
  ≪□Set≫ .idn₀ {𝒳} .ap₀ x = x
  ≪□Set≫ .idn₀ {𝒳} .ap₁ p = p
  ≪□Set≫ .idn₀ {𝒳} .ap₂ f = idn 𝒳
  ≪□Set≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₀ x = ap₀ G (ap₀ F x)
  ≪□Set≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₁ p = ap₁ G (ap₁ F p)
  ≪□Set≫ .cmp₀ {𝒳}{𝒴}{𝒵} G F .ap₂ f = cmp 𝒵 (ap₂ G f) (ap₁ G (ap₂ F f))
  ≪□Set≫ .idn₁ {𝒳}{𝒴}{F}{Γ}{x} = idn 𝒴 {Γ} {ap₀ F x}
  ≪□Set≫ .cmp₁ {𝒳}{𝒴}{F}{G}{H} β α {Γ}{x} = cmp 𝒴 {Γ} (β {Γ}{x}) (α {Γ}{x})
  ≪□Set≫ .inv₁ {𝒳}{𝒴}{F}{G} α {Γ}{x} = inv 𝒴 {Γ} (α {Γ}{x})
  ≪□Set≫ .cmp₀* {𝒳}{𝒴}{𝒵}{F₀}{F₁}{G₀}{G₁} β α {Γ}{x} = cmp 𝒵 {Γ} (β {Γ}{ap₀ F₁ x}) (ap₁ G₀ (α {Γ}{x}))
  ≪□Set≫ .coh-λ {𝒳}{𝒴}{F}{Γ}{x} = idn 𝒴
  ≪□Set≫ .coh-ρ {𝒳}{𝒴}{F}{Γ}{x} = idn 𝒴
  ≪□Set≫ .coh-α {𝒲}{𝒳}{𝒴}{𝒵}{F}{G}{H}{Γ}{x} = idn 𝒵

  -- the formal or representable cube
  □ : Symbols → □Set
  □ Δ .obj Γ = Sub Γ Δ
  □ Δ .hom Γ = Cube._≅_
  □ Δ .idn = 𝕀.idn refl
  □ Δ .cmp β α {i} = 𝕀.cmp (β {i}) (α {i})
  □ Δ .inv α {i} = 𝕀.inv (α {i})
  □ Δ .sub f = λ g → g ≫=≫ f
  □ Δ .sub-idn = 𝕀.idn Cube.idn
  □ Δ .sub-cmp {x = h} g f {i} = 𝕀.idn (Cube.ass (look h i) f g)
  □ Δ .sub-rsp {x = h₀}{h₁} f g α β {i} = Cube.rsp (look h₀ i) (look h₁ i) f g (β {i}) α

  -- the interval in HIT style
  data Interval (I : Symbols) : Set where
    west : Interval I
    east : Interval I
    walk : (φ : 𝕀 I) → Interval I

  interval : □Set
  interval .obj = Interval
  interval .hom I east east = T.𝟙
  interval .hom I east (walk φ₁) = #1 𝕀.≅ φ₁
  interval .hom I (walk φ₀) east = φ₀ 𝕀.≅ #1
  interval .hom I (walk φ₀) (walk φ₁) = φ₀ 𝕀.≅ φ₁
  interval .hom I (walk φ₀) west = φ₀ 𝕀.≅ #0
  interval .hom I west (walk φ₁) = #0 𝕀.≅ φ₁
  interval .hom I west west = T.𝟙
  interval .hom I _ _ = T.𝟘
  interval .idn {x = west} = *
  interval .idn {x = east} = *
  interval .idn {x = walk φ} = 𝕀.idn refl
  interval .cmp {x = west} {west} {west} * * = *
  interval .cmp {x = west} {west} {east} () *
  interval .cmp {x = west} {west} {walk φ₂} q * = q
  interval .cmp {x = west} {east} {west} () ()
  interval .cmp {x = west} {east} {east} * ()
  interval .cmp {x = west} {east} {walk φ₂} q ()
  interval .cmp {x = west} {walk φ₁} {west} q p = *
  interval .cmp {x = west} {walk φ₁} {east} q p = 𝕀.distinct (𝕀.cmp q p)
  interval .cmp {x = west} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {x = east} {west} {west} * ()
  interval .cmp {x = east} {west} {east} () ()
  interval .cmp {x = east} {west} {walk φ₂} q ()
  interval .cmp {x = east} {east} {west} () *
  interval .cmp {x = east} {east} {east} * * = *
  interval .cmp {x = east} {east} {walk φ₂} q * = q
  interval .cmp {x = east} {walk φ₁} {west} q p = 𝕀.distinct (𝕀.cmp (𝕀.inv p) (𝕀.inv q))
  interval .cmp {x = east} {walk φ₁} {east} q p = *
  interval .cmp {x = east} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {x = walk φ₀} {west} {west} * p = p
  interval .cmp {x = walk φ₀} {west} {east} () p
  interval .cmp {x = walk φ₀} {west} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {x = walk φ₀} {east} {west} () p
  interval .cmp {x = walk φ₀} {east} {east} * p = p
  interval .cmp {x = walk φ₀} {east} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {x = walk φ₀} {walk φ₁} {west} q p = 𝕀.cmp q p
  interval .cmp {x = walk φ₀} {walk φ₁} {east} q p = 𝕀.cmp q p
  interval .cmp {x = walk φ₀} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .inv {x = west} {west} * = *
  interval .inv {x = west} {east} ()
  interval .inv {x = west} {walk φ₁} p = 𝕀.inv p
  interval .inv {x = east} {west} ()
  interval .inv {x = east} {east} * = *
  interval .inv {x = east} {walk φ₁} p = 𝕀.inv p
  interval .inv {x = walk φ₀} {west} p = 𝕀.inv p
  interval .inv {x = walk φ₀} {east} p = 𝕀.inv p
  interval .inv {x = walk φ₀} {walk φ₁} p = 𝕀.inv p
  interval .sub f west = west
  interval .sub f east = east
  interval .sub f (walk φ) = walk (φ ≫= f)
  interval .sub-idn {x = west} = *
  interval .sub-idn {x = east} = *
  interval .sub-idn {x = walk φ} = 𝕀.idn Cube.idn
  interval .sub-cmp {x = west} g f = *
  interval .sub-cmp {x = east} g f = *
  interval .sub-cmp {x = walk φ} g f = 𝕀.idn (Cube.ass φ f g)
  interval .sub-rsp {x = west} {west} f p α β = *
  interval .sub-rsp {x = west} {east} f p α ()
  interval .sub-rsp {x = west} {walk φ₁} f p α β = Cube.rsp-lhs p β
  interval .sub-rsp {x = east} {west} f p α ()
  interval .sub-rsp {x = east} {east} f p α β = *
  interval .sub-rsp {x = east} {walk φ₁} f p α β = Cube.rsp-lhs p β
  interval .sub-rsp {x = walk φ₀} {west} f p α β = Cube.rsp-lhs f β
  interval .sub-rsp {x = walk φ₀} {east} f p α β = Cube.rsp-lhs f β
  interval .sub-rsp {x = walk φ₀} {walk φ₁} f p α β = Cube.rsp φ₀ φ₁ f p β α

  -- walk "a" ≅ west (under {"a" ≔ #0})
  ϕ₀ :
    hom interval []
      (sub interval ("a" ≔ #0 ∷ []) (walk ≪ "a" ≫))
      west
  ϕ₀ = 𝕀.idn refl

  -- walk (¬ "a" ∨ "b") ≅ east (under {"a" ≔ #0; "b" ≔ #0})
  ϕ₁ :
    hom interval []
      (sub interval ("a" ≔ #0 ∷ "b" ≔ #0 ∷ []) (walk (¬ ≪ "a" ≫ ∨ ≪ "b" ≫)))
      east
  ϕ₁ = 𝕀.cmp 𝕀.¬-#0 𝕀.∨-uni
open Flattened public
  hiding (module □Set)

module Equivalence where
  open Setoid

  fwd : Presheaf.□Set → Flattened.□Set
  fwd F .obj Γ = obj (ap₀ F Γ)
  fwd F .hom Γ = hom (ap₀ F Γ)
  fwd F .idn {Γ} = idn (ap₀ F Γ)
  fwd F .cmp {Γ} = cmp (ap₀ F Γ)
  fwd F .inv {Γ} = inv (ap₀ F Γ)
  fwd F .sub f = ap₀ (ap₁ F f)
  fwd F .sub-idn = coh-idn F
  fwd F .sub-cmp g f = coh-cmp F g f
  fwd F .sub-rsp {Γ}{Δ} f g α β = cmp (ap₀ F Δ) (ap₂ F α) (ap₁ (ap₁ F f) β)

  bwd : Flattened.□Set → Presheaf.□Set
  bwd F .ap₀ Γ .obj = obj F Γ
  bwd F .ap₀ Γ .hom = hom F Γ
  bwd F .ap₀ Γ .idn = idn F
  bwd F .ap₀ Γ .cmp = cmp F
  bwd F .ap₀ Γ .inv = inv F
  bwd F .ap₁ f .ap₀ x = sub F f x
  bwd F .ap₁ f .ap₁ α = sub-rsp F f f (𝕀.idn refl) α
  bwd F .ap₂ {Γ}{Δ}{f}{g} α = sub-rsp F f g α (idn F)
  bwd F .coh-idn = sub-idn F
  bwd F .coh-cmp g f = sub-cmp F g f
