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

  -- the formal or representable cube
  □ : Symbols → □Set
  □ = ap₀ (Yo Cube.cat)

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
        : ∀ {Γ A}
        → hom Γ A A
      cmp
        : ∀ {Γ A B C}
        → (q : hom Γ B C)
        → (p : hom Γ A B)
        → hom Γ A C
      inv
        : ∀ {Γ A B}
        → (p : hom Γ A B)
        → hom Γ B A
    field -- substitution across fibers
      sub
        : ∀ {Γ Δ}
        → (f : Sub Δ Γ)
        → obj Γ → obj Δ
      sub-idn
        : ∀ {Γ A}
        → hom Γ (sub loop A) A
      sub-cmp
        : ∀ {Γ Δ Θ A}
        → (g : Sub Θ Δ)
        → (f : Sub Δ Γ)
        → hom Θ (sub (f ≫=≫ g) A) (sub g (sub f A))
      sub-rsp -- functoriality or whiskering
        : ∀ {Γ Δ A B}
        → (f g : Sub Δ Γ)
        → (α : f Cube.≅ g)
        → (β : hom Γ A B)
        → hom Δ (sub f A) (sub g B)
  open □Set public

  -- the formal or representable cube
  □ : Symbols → □Set
  □ Δ .obj Γ = Sub Γ Δ
  □ Δ .hom Γ = Cube._≅_
  □ Δ .idn = 𝕀.idn refl
  □ Δ .cmp β α {i} = 𝕀.cmp (β {i}) (α {i})
  □ Δ .inv α {i} = 𝕀.inv (α {i})
  □ Δ .sub f = λ g → g ≫=≫ f
  □ Δ .sub-idn = 𝕀.idn Cube.idn
  □ Δ .sub-cmp {A = A} g f {i} = 𝕀.idn (Cube.ass (look A i) f g)
  □ Δ .sub-rsp {A = A}{B} f g α β {i} = Cube.rsp (look A i) (look B i) f g (β {i}) α

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
  interval .idn {A = west} = *
  interval .idn {A = east} = *
  interval .idn {A = walk φ} = 𝕀.idn refl
  interval .cmp {A = west} {west} {west} * * = *
  interval .cmp {A = west} {west} {east} () *
  interval .cmp {A = west} {west} {walk φ₂} q * = q
  interval .cmp {A = west} {east} {west} () ()
  interval .cmp {A = west} {east} {east} * ()
  interval .cmp {A = west} {east} {walk φ₂} q ()
  interval .cmp {A = west} {walk φ₁} {west} q p = *
  interval .cmp {A = west} {walk φ₁} {east} q p = 𝕀.distinct (𝕀.cmp q p)
  interval .cmp {A = west} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {A = east} {west} {west} * ()
  interval .cmp {A = east} {west} {east} () ()
  interval .cmp {A = east} {west} {walk φ₂} q ()
  interval .cmp {A = east} {east} {west} () *
  interval .cmp {A = east} {east} {east} * * = *
  interval .cmp {A = east} {east} {walk φ₂} q * = q
  interval .cmp {A = east} {walk φ₁} {west} q p = 𝕀.distinct (𝕀.cmp (𝕀.inv p) (𝕀.inv q))
  interval .cmp {A = east} {walk φ₁} {east} q p = *
  interval .cmp {A = east} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {A = walk φ₀} {west} {west} * p = p
  interval .cmp {A = walk φ₀} {west} {east} () p
  interval .cmp {A = walk φ₀} {west} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {A = walk φ₀} {east} {west} () p
  interval .cmp {A = walk φ₀} {east} {east} * p = p
  interval .cmp {A = walk φ₀} {east} {walk φ₂} q p = 𝕀.cmp q p
  interval .cmp {A = walk φ₀} {walk φ₁} {west} q p = 𝕀.cmp q p
  interval .cmp {A = walk φ₀} {walk φ₁} {east} q p = 𝕀.cmp q p
  interval .cmp {A = walk φ₀} {walk φ₁} {walk φ₂} q p = 𝕀.cmp q p
  interval .inv {A = west} {west} * = *
  interval .inv {A = west} {east} ()
  interval .inv {A = west} {walk φ₁} p = 𝕀.inv p
  interval .inv {A = east} {west} ()
  interval .inv {A = east} {east} * = *
  interval .inv {A = east} {walk φ₁} p = 𝕀.inv p
  interval .inv {A = walk φ₀} {west} p = 𝕀.inv p
  interval .inv {A = walk φ₀} {east} p = 𝕀.inv p
  interval .inv {A = walk φ₀} {walk φ₁} p = 𝕀.inv p
  interval .sub f west = west
  interval .sub f east = east
  interval .sub f (walk φ) = walk (φ ≫= f)
  interval .sub-idn {A = west} = *
  interval .sub-idn {A = east} = *
  interval .sub-idn {A = walk φ} = 𝕀.idn Cube.idn
  interval .sub-cmp {A = west} g f = *
  interval .sub-cmp {A = east} g f = *
  interval .sub-cmp {A = walk φ} g f = 𝕀.idn (Cube.ass φ f g)
  interval .sub-rsp {A = west} {west} f p α β = *
  interval .sub-rsp {A = west} {east} f p α ()
  interval .sub-rsp {A = west} {walk φ₁} f p α β = Cube.rsp-lhs p β
  interval .sub-rsp {A = east} {west} f p α ()
  interval .sub-rsp {A = east} {east} f p α β = *
  interval .sub-rsp {A = east} {walk φ₁} f p α β = Cube.rsp-lhs p β
  interval .sub-rsp {A = walk φ₀} {west} f p α β = Cube.rsp-lhs f β
  interval .sub-rsp {A = walk φ₀} {east} f p α β = Cube.rsp-lhs f β
  interval .sub-rsp {A = walk φ₀} {walk φ₁} f p α β = Cube.rsp φ₀ φ₁ f p β α

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
