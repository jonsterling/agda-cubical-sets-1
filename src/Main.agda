{-# OPTIONS --type-in-type #-}

module Main where

open import Category
open import Globular
open import Prelude
  hiding (¬_)

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

  record Names (X : Symbols) : Set where
    constructor pt
    field
      x : String
      el : x ∈ X
  open Names public
open Symbols public

module 𝕀 where
  infix  0 _≅_
  infix  4 ¬_
  infixr 2 _∨_
  infixr 3 _∧_

  data 𝕀 (Γ : Symbols) : Set where
    var : (i : Names Γ) → 𝕀 Γ
    #0 : 𝕀 Γ
    #1 : 𝕀 Γ
    _∨_ : (a b : 𝕀 Γ) → 𝕀 Γ
    _∧_ : (a b : 𝕀 Γ) → 𝕀 Γ
    ¬_ : (a : 𝕀 Γ) → 𝕀 Γ

  data 𝕀/# (Γ : Symbols) : Set where
    #0 : 𝕀/# Γ
    #1 : 𝕀/# Γ

  data 𝕀/? (Γ : Symbols) : Set where
    var : (i : Names Γ) → 𝕀/? Γ
    ¬_ : (i : Names Γ) → 𝕀/? Γ

  data 𝕀/∧ (Γ : Symbols) : Set where
    _∧_ : 𝕀/? Γ → 𝕀/∧ Γ → 𝕀/∧ Γ
    ?[_] : 𝕀/? Γ → 𝕀/∧ Γ

  data 𝕀/∨ (Γ : Symbols) : Set where
    _∨_ : 𝕀/∧ Γ → 𝕀/∨ Γ → 𝕀/∨ Γ
    ∧[_] : 𝕀/∧ Γ → 𝕀/∨ Γ
    #[_] : 𝕀/# Γ → 𝕀/∨ Γ

  _[∨]_ : ∀ {Γ} → 𝕀/∨ Γ → 𝕀/∨ Γ → 𝕀/∨ Γ
  (a ∨ b) [∨] c = a ∨ (b [∨] c)
  ∧[ a ] [∨] b = a ∨ b
  #[ #0 ] [∨] b = b
  #[ #1 ] [∨] b = #[ #1 ]

  _[∧]_ : ∀ {Γ} → 𝕀/∧ Γ → 𝕀/∧ Γ → 𝕀/∧ Γ
  (a ∧ b) [∧] c = a ∧ (b [∧] c)
  ?[ a ] [∧] c = a ∧ c

  _[∧]ᵛ_ : ∀ {Γ} → 𝕀/∧ Γ → 𝕀/∨ Γ → 𝕀/∨ Γ
  a [∧]ᵛ (b ∨ c) = (a [∧] b) ∨ (a [∧]ᵛ c)
  a [∧]ᵛ ∧[ b ] = ∧[ a [∧] b ]
  a [∧]ᵛ #[ #0 ] = #[ #0 ]
  a [∧]ᵛ #[ #1 ] = ∧[ a ]

  _ᵛ[∧]ᵛ_ : ∀ {Γ} → 𝕀/∨ Γ → 𝕀/∨ Γ → 𝕀/∨ Γ
  (a ∨ b) ᵛ[∧]ᵛ c = (a [∧]ᵛ c) [∨] (b ᵛ[∧]ᵛ c)
  ∧[ a ] ᵛ[∧]ᵛ b = a [∧]ᵛ b
  #[ #0 ] ᵛ[∧]ᵛ b = #[ #0 ]
  #[ #1 ] ᵛ[∧]ᵛ b = b

  [¬]?_ : ∀ {Γ} → 𝕀/? Γ → 𝕀/? Γ
  [¬]? var i = ¬ i
  [¬]? (¬ i) = var i

  [¬]^_ : ∀ {Γ} → 𝕀/∧ Γ → 𝕀/∧ Γ
  [¬]^ (a ∧ b) = ([¬]? a) ∧ [¬]^ b
  [¬]^ ?[ a ] = ?[ [¬]? a ]

  [¬]_ : ∀ {Γ} → 𝕀/∨ Γ → 𝕀/∨ Γ
  [¬] (a ∨ b) = ([¬]^ a) [∧]ᵛ ([¬] b)
  [¬] ∧[ a ] = ∧[ [¬]^ a ]
  [¬] #[ #0 ] = #[ #1 ]
  [¬] #[ #1 ] = #[ #0 ]

  eval : ∀ {Γ} → 𝕀 Γ → 𝕀/∨ Γ
  eval (var i) = ∧[ ?[ var i ] ]
  eval #0 = #[ #0 ]
  eval #1 = #[ #1 ]
  eval (a ∨ b) = eval a [∨] eval b
  eval (a ∧ b) = eval a ᵛ[∧]ᵛ eval b
  eval (¬ a) = [¬] eval a

  quo/? : ∀ {Γ} → 𝕀/? Γ → 𝕀 Γ
  quo/? (var i) = var i
  quo/? (¬ i) = ¬ (var i)

  quo/∧ : ∀ {Γ} → 𝕀/∧ Γ → 𝕀 Γ
  quo/∧ (a ∧ b) = quo/? a ∧ quo/∧ b
  quo/∧ ?[ a ] = quo/? a

  quo/# : ∀ {Γ} → 𝕀/# Γ → 𝕀 Γ
  quo/# #0 = #0
  quo/# #1 = #1

  quo : ∀ {Γ} → 𝕀/∨ Γ → 𝕀 Γ
  quo (a ∨ b) = (quo/∧ a) ∧ (quo b)
  quo ∧[ a ] = quo/∧ a
  quo #[ a ] = quo/# a

  norm : ∀ {Γ} → 𝕀 Γ → 𝕀 Γ
  norm a = quo (eval a)



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
    seq -- composition (diagrammatic order)
      : ∀ {a b c}
      → (p : a ≅ b)
      → (q : b ≅ c)
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

module Sub where
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
    look : ∀ {Γ Δ} → Sub Δ Γ → Names Γ → 𝕀 Δ
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
  rsp-lhs f (𝕀.seq p q) = 𝕀.seq (rsp-lhs f p) (rsp-lhs f q)
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
  rsp a b f g α β = 𝕀.seq (rsp-lhs f α) (rsp-rhs b f g β)

  -- the category of nominal cubes
  cat : Category
  quiver cat .● = Symbols
  quiver cat .∂ Γ Δ .● = Sub Δ Γ
  quiver cat .∂ Γ Δ .∂ f g .● = f ≅ g
  quiver cat .∂ Γ Δ .∂ f g .∂ α β = Void
  idn₀ cat = loop
  seq₀ cat = _≫=≫_
  idn₁ cat = 𝕀.idn refl
  seq₁ cat α β {i} = 𝕀.seq (α {i}) (β {i})
  inv₁ cat α {i} = 𝕀.inv (α {i})
  seq₀* cat {f₀ = f₀}{f₁}{g₀}{g₁} α β {i} = rsp (look f₀ i) (look f₁ i) g₀ g₁ (α {i}) β
  coh-λ cat = 𝕀.idn refl
  coh-ρ cat = 𝕀.idn idn
  coh-α cat {f = f}{g}{h}{i} = 𝕀.idn (ass (look f i) g h)
open Sub
  hiding (module Sub)
  using (Sub)
  using ([])
  using (_∷_)
  using (_≔_)
  using (_≫=_)
  using (_≫=≫_)
  using (look)
  using (loop)

module □Set where
  record □Set : Set where
    no-eta-equality
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
      seq
        : ∀ {Γ A B C}
        → (p : hom Γ A B)
        → (q : hom Γ B C)
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
      sub-seq
        : ∀ {Γ Δ Θ A}
        → (f : Sub Θ Γ)
        → (g : Sub Δ Θ)
        → hom Δ (sub (f ≫=≫ g) A) (sub g (sub f A))
      sub-rsp -- functoriality or whiskering
        : ∀ {Γ Δ A B}
        → (f g : Sub Δ Γ)
        → (α : f Sub.≅ g)
        → (β : hom Γ A B)
        → hom Δ (sub f A) (sub g B)
  open □Set public
open □Set public
  hiding (module □Set)

-- the formal or representable Γ-cube
□ : Symbols → □Set
obj (□ Γ) Δ = Sub Δ Γ
hom (□ Γ) Δ = Sub._≅_
idn (□ Γ) = 𝕀.idn refl
seq (□ Γ) p q = 𝕀.seq p q
inv (□ Γ) p = 𝕀.inv p
sub (□ Γ) f g = g ≫=≫ f
sub-idn (□ Γ) = 𝕀.idn Sub.idn
sub-seq (□ Γ) {A = A} f g = 𝕀.idn (Sub.ass (look A _) f g)
sub-rsp (□ Γ) {A = A}{B} f g α β {i} = Sub.rsp (look A i) (look B i) f g β α

-- the interval in HIT style
data Interval (I : Symbols) : Set where
  west : Interval I
  east : Interval I
  walk : (φ : 𝕀 I) → Interval I

interval : □Set
obj interval = Interval
hom interval I west west = T.𝟙
hom interval I east east = T.𝟙
hom interval I west (walk φ₁) = φ₁ 𝕀.≅ #0
hom interval I east (walk φ₁) = φ₁ 𝕀.≅ #1
hom interval I (walk φ₀) west = φ₀ 𝕀.≅ #0
hom interval I (walk φ₀) east = φ₀ 𝕀.≅ #1
hom interval I (walk φ₀) (walk φ₁) = φ₀ 𝕀.≅ φ₁
hom interval I _ _ = T.𝟘
idn interval {A = west} = *
idn interval {A = east} = *
idn interval {A = walk φ} = 𝕀.idn refl
seq interval {A = west} {west} {west} p q = *
seq interval {A = west} {west} {east} p ()
seq interval {A = west} {west} {walk φ} p q = q
seq interval {A = west} {east} {C} () q
seq interval {A = west} {walk φ₁} {west} p q = *
seq interval {A = west} {walk φ₁} {east} p q = 𝕀.distinct (𝕀.seq (𝕀.inv p) q)
seq interval {A = west} {walk φ₁} {walk φ₂} p q = 𝕀.seq (𝕀.inv q) p
seq interval {A = east} {west} {C} () q
seq interval {A = east} {east} {west} p ()
seq interval {A = east} {east} {east} p q = *
seq interval {A = east} {east} {walk φ} p q = q
seq interval {A = east} {walk φ₁} {west} p q = 𝕀.distinct (𝕀.seq (𝕀.inv q) p)
seq interval {A = east} {walk φ₁} {east} p q = *
seq interval {A = east} {walk φ₁} {walk φ₂} p q = 𝕀.seq (𝕀.inv q) p
seq interval {A = walk φ₀} {west} {west} p q = p
seq interval {A = walk φ₀} {west} {east} p ()
seq interval {A = walk φ₀} {west} {walk φ₂} p q = 𝕀.seq p (𝕀.inv q)
seq interval {A = walk φ₀} {east} {west} p ()
seq interval {A = walk φ₀} {east} {east} p q = p
seq interval {A = walk φ₀} {east} {walk φ₂} p q = 𝕀.seq p (𝕀.inv q)
seq interval {A = walk φ₀} {walk φ₁} {west} p q = 𝕀.seq p q
seq interval {A = walk φ₀} {walk φ₁} {east} p q = 𝕀.seq p q
seq interval {A = walk φ₀} {walk φ₁} {walk φ₂} p q = 𝕀.seq p q
inv interval {A = west} {west} p = *
inv interval {A = west} {east} ()
inv interval {A = west} {walk φ₁} p = p
inv interval {A = east} {west} ()
inv interval {A = east} {east} p = *
inv interval {A = east} {walk φ₁} p = p
inv interval {A = walk φ₀} {west} p = p
inv interval {A = walk φ₀} {east} p = p
inv interval {A = walk φ₀} {walk φ₁} p = 𝕀.inv p
sub interval f west = west
sub interval f east = east
sub interval f (walk φ) = walk (φ ≫= f)
sub-idn interval {A = west} = *
sub-idn interval {A = east} = *
sub-idn interval {A = walk φ} = 𝕀.idn Sub.idn
sub-seq interval {A = west} f g = *
sub-seq interval {A = east} f g = *
sub-seq interval {A = walk φ} f g = 𝕀.idn (Sub.ass φ f g)
sub-rsp interval {A = west} {west} f p α β = *
sub-rsp interval {A = west} {east} f p α ()
sub-rsp interval {A = west} {walk φ₁} f p α β = Sub.rsp φ₁ #0 p p β (𝕀.idn refl)
sub-rsp interval {A = east} {west} f p α ()
sub-rsp interval {A = east} {east} f p α β = *
sub-rsp interval {A = east} {walk φ₁} f p α β = Sub.rsp φ₁ #1 p f β (𝕀.inv α)
sub-rsp interval {A = walk φ₀} {west} f p α β = Sub.rsp φ₀ #0 f p β α
sub-rsp interval {A = walk φ₀} {east} f p α β = Sub.rsp φ₀ #1 f p β α
sub-rsp interval {A = walk φ₀} {walk φ₁} f p α β = Sub.rsp φ₀ φ₁ f p β α

-- example: walk "a" ≅ west (given {"a" ≔ #0})
ϕ₀ : hom interval [] (sub interval ("a" ≔ #0 ∷ []) (walk ≪ "a" ≫)) west
ϕ₀ = 𝕀.idn refl

-- example: walk (¬ "a" ∨ "b") ≅ east (given {"a" ≔ #0, "b" ≔ #0})
ϕ₁ : hom interval []
  (sub interval ("a" ≔ #0 ∷ "b" ≔ #0 ∷ []) (walk (¬ ≪ "a" ≫ ∨ ≪ "b" ≫)))
  east
ϕ₁ = 𝕀.seq 𝕀.∨-uni 𝕀.¬-#0
