{-# OPTIONS --type-in-type #-}

module Main where

open import Prelude

infix  1 _∈_
infix  0 _⇔_

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

record _⇔_ (A B : Set) : Set where
  no-eta-equality
  constructor eqv
  field
    into : A → B
    from : B → A
open _⇔_ public

module ≅ where
  _≅_ : Symbols → Symbols → Set
  xs ≅ ys = ∀ {a} → a ∈ xs ⇔ a ∈ ys

  idn : ∀ {xs} → xs ≅ xs
  into idn a∈xs = a∈xs
  from idn a∈xs = a∈xs

  seq : ∀ {xs ys zs} → xs ≅ ys → ys ≅ zs → xs ≅ zs
  into (seq xs≅ys ys≅zs) a∈xs = into ys≅zs (into xs≅ys a∈xs)
  from (seq xs≅ys ys≅zs) a∈zs = from xs≅ys (from ys≅zs a∈zs)

  inv : ∀ {xs ys} → xs ≅ ys → ys ≅ xs
  into (inv xs≅ys) a∈ys = from xs≅ys a∈ys
  from (inv xs≅ys) a∈xs = into xs≅ys a∈xs
open ≅
  using (_≅_)

module DeMorgan where
  infixl 0 _≫=_
  infixr 0 _≫=≫_

  data DeMorgan (X : Symbols) : Set where
    var : (x : Names X) → DeMorgan X
    #0 : DeMorgan X
    #1 : DeMorgan X
    or : (a b : DeMorgan X) → DeMorgan X
    and : (a b : DeMorgan X) → DeMorgan X
    not : (a : DeMorgan X) → DeMorgan X

  data rel {X} : (a b : DeMorgan X) → Set where
    rel-idn
      : ∀ {a b}
      → a ≡ b
      → rel a b
    rel-seq
      : ∀ {a b c}
      → (p : rel a b)
      → (q : rel b c)
      → rel a c
    rel-inv
      : ∀ {a b}
      → (p : rel a b)
      → rel b a
    or-abs
      : ∀ {a b}
      → rel (or a (and a b)) a
    or-ass
      : ∀ {a b c}
      → rel (or a (or b c)) (or (or a b) c)
    or-com
      : ∀ {a b}
      → rel (or a b) (or b a)
    or-dis
      : ∀ {a b c}
      → rel (or a (and b c)) (and (or a b) (or a c))
    or-ide
      : ∀ {a}
      → rel (or a a) a
    or-rsp
      : ∀ {a₀ a₁ b₀ b₁}
      → rel a₀ a₁
      → rel b₀ b₁
      → rel (or a₀ b₀) (or a₁ b₁)
    or-uni
      : ∀ {a}
      → rel (or a #0) a
    and-abs
      : ∀ {a b}
      → rel (and a (or a b)) a
    and-ass
      : ∀ {a b c}
      → rel (and a (and b c)) (and (and a b) c)
    and-com
      : ∀ {a b}
      → rel (and a b) (and b a)
    and-dis
      : ∀ {a b c}
      → rel (and a (or b c)) (or (and a b) (and a c))
    and-ide
      : ∀ {a}
      → rel (and a a) a
    and-rsp
      : ∀ {a₀ a₁ b₀ b₁}
      → rel a₀ a₁
      → rel b₀ b₁
      → rel (and a₀ b₀) (and a₁ b₁)
    and-uni
      : ∀ {a}
      → rel (and a #1) a
    not-dis
      : ∀ {a b}
      → rel (not (and a b)) (or (not a) (not b))
    not-inv
      : ∀ {a}
      → rel (not (not a)) a
    not-rsp
      : ∀ {a₀ a₁}
      → rel a₀ a₁
      → rel (not a₀) (not a₁)

  data Sub (J : Symbols) : (I : Symbols) → Set where
    stop
      : Sub J []
    step
      : ∀ {𝒾 I}
      → (𝔡 : DeMorgan J)
      → (σ : Sub J I)
      → Sub J (𝒾 ∷ I)
    loop
      : Sub J J
    _≫=≫_
      : ∀ {I K}
      → (f : Sub K I)
      → (g : Sub J K)
      → Sub J I

  mutual
    look : ∀ {I J} → Sub J I → Names I → DeMorgan J
    look (stop) (pt _ ())
    look (step 𝔡 _) (pt _ (stop)) = 𝔡
    look (step _ f) (pt x (step _ _ ε)) = look f (pt x ε)
    look (loop) ε = var ε
    look (f ≫=≫ g) ε = look f ε ≫= g

    _≫=_ : ∀ {I J} → DeMorgan I → Sub J I → DeMorgan J
    var x ≫= f = look f x
    #0 ≫= f = #0
    #1 ≫= f = #1
    or a b ≫= f = or (a ≫= f) (b ≫= f)
    and a b ≫= f = and (a ≫= f) (b ≫= f)
    not a ≫= f = not (a ≫= f)

  _≃_ : ∀ {J I} (f g : Sub J I) → Set
  f ≃ g = ∀ {𝒾} → rel (look f 𝒾) (look g 𝒾)

  ≫=-λ
    : {I J : Symbols} {a b : DeMorgan I}
    → (f : Sub J I)
    → rel a b
    → rel (a ≫= f) (b ≫= f)
  ≫=-λ f (rel-idn refl) = rel-idn refl
  ≫=-λ f (rel-seq p q) = rel-seq (≫=-λ f p) (≫=-λ f q)
  ≫=-λ f (rel-inv p) = rel-inv (≫=-λ f p)
  ≫=-λ f or-abs = or-abs
  ≫=-λ f or-ass = or-ass
  ≫=-λ f or-com = or-com
  ≫=-λ f or-dis = or-dis
  ≫=-λ f or-ide = or-ide
  ≫=-λ f (or-rsp p q) = or-rsp (≫=-λ f p) (≫=-λ f q)
  ≫=-λ f or-uni = or-uni
  ≫=-λ f and-abs = and-abs
  ≫=-λ f and-ass = and-ass
  ≫=-λ f and-com = and-com
  ≫=-λ f and-dis = and-dis
  ≫=-λ f and-ide = and-ide
  ≫=-λ f (and-rsp p q) = and-rsp (≫=-λ f p) (≫=-λ f q)
  ≫=-λ f and-uni = and-uni
  ≫=-λ f not-dis = not-dis
  ≫=-λ f not-inv = not-inv
  ≫=-λ f (not-rsp p) = not-rsp (≫=-λ f p)

  postulate
    ≫=-ρ
      : ∀ {I J} a
      → (f g : Sub J I)
      → f ≃ g
      → rel (a ≫= f) (a ≫= g)

  ≫=-α
    : ∀ {I J K}
    → (a : DeMorgan I)
    → (f : Sub J I)
    → (g : Sub K J)
    → ((a ≫= f) ≫= g) ≡ (a ≫= (f ≫=≫ g))
  ≫=-α (var _) f g = refl
  ≫=-α #0 f g = refl
  ≫=-α #1 f g = refl
  ≫=-α (or a b) f g = ≡.ap² or (≫=-α a f g) (≫=-α b f g)
  ≫=-α (and a b) f g = ≡.ap² and (≫=-α a f g) (≫=-α b f g)
  ≫=-α (not a) f g = ≡.ap not (≫=-α a f g)
open DeMorgan public
  hiding (module DeMorgan)

record □Set : Set where
  no-eta-equality
  field
    fib₀
      : (I : Symbols)
      → Set
    fib₁
      : ∀ I
      → fib₀ I → fib₀ I → Set
  field
    coe₀
      : ∀ {I J}
      → (f : Sub I J)
      → (a : fib₀ I) → fib₀ J
    coe₁
      : ∀ {I J A B}
      → (f : Sub I J)
      → (p : fib₁ I A B)
      → fib₁ J (coe₀ f A) (coe₀ f B)
  field
    fib-idn
      : ∀ {I A}
      → fib₁ I A A
    fib-seq
      : ∀ {I A B C}
      → (p : fib₁ I A B)
      → (q : fib₁ I B C)
      → fib₁ I A C
    fib-inv
      : ∀ {I A B}
      → (p : fib₁ I A B)
      → fib₁ I B A
  field
    coe-idn
      : ∀ {I A}
      → fib₁ I (coe₀ loop A) A
    coe-seq
      : ∀ {I J K A}
      → (f : Sub I J)
      → (g : Sub J K)
      → fib₁ K (coe₀ (g ≫=≫ f) A) (coe₀ g (coe₀ f A))
    coe-rel
      : ∀ {I J A}
      → {f g : Sub I J}
      → (φ : f ≃ g)
      → fib₁ J (coe₀ f A) (coe₀ g A)
open □Set public

-- FIXME
□ : Symbols → □Set
fib₀ (□ I) J = Sub I J
fib₁ (□ I) J = _≃_
coe₀ (□ I) = _≫=≫_
coe₁ (□ I) {J}{K}{f}{g} k p {𝓁} = ≫=-ρ (look k 𝓁) f g p
fib-idn (□ I) = rel-idn refl
fib-seq (□ I) p q = rel-seq p q
fib-inv (□ I) p = rel-inv p
coe-idn (□ I) = rel-idn refl
coe-seq (□ I) {A = A} f g {𝒾} = rel-idn (≫=-α (look g 𝒾) f A)
coe-rel (□ I) {A = A} φ = ≫=-λ A φ
