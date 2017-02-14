{-# OPTIONS --type-in-type #-}

module Main where

open import Prelude

infix  0 _∉_
infix  1 _∈_
infix  0 _⇔_

mutual
  data Symbols : Set where
    nil : Symbols
    cons : (x : String) (xs : Symbols) (φ : x ∉ xs) → Symbols

  _∉_ : String → Symbols → Set
  x ∉ nil = T.𝟙
  x ∉ cons y xs _ with x String.≟ y
  … | no  _ = x ∉ xs
  … | yes _ = T.𝟘

data _∈_ (x : String) : Symbols → Set where
  stop
    : ∀ {xs φ}
    → x ∈ cons x xs φ
  step
    : ∀ {y xs φ}
    → x ∈ xs
    → x ∈ cons y xs φ

record Names (X : Symbols) : Set where
  constructor pt
  field
    {x} : String
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
    ret : (x : Names X) → DeMorgan X
    #0 : DeMorgan X
    #1 : DeMorgan X
    or : (a b : DeMorgan X) → DeMorgan X
    and : (a b : DeMorgan X) → DeMorgan X
    not : (a : DeMorgan X) → DeMorgan X

  data rel {X} : (a b : DeMorgan X) → Set where
    rel-idn
      : ∀ {a}
      → rel a a
    rel-seq
      : ∀ {a b c}
      → rel a b
      → rel b c
      → rel a c
    rel-inv
      : ∀ {a b}
      → rel a b
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
    and-uni
      : ∀ {a}
      → rel (and a #1) a
    not-dis
      : ∀ {a b}
      → rel (not (and a b)) (or (not a) (not b))
    not-inv
      : ∀ {a}
      → rel (not (not a)) a

  -- FIXME: defunctionalize
  Sub : Symbols → Symbols → Set
  Sub J I = Names I → DeMorgan J

  _≫=_ : ∀ {I J} → DeMorgan I → Sub J I → DeMorgan J
  ret x ≫= f = f x
  #0 ≫= f = #0
  #1 ≫= f = #1
  or a b ≫= f = or (a ≫= f) (b ≫= f)
  and a b ≫= f = and (a ≫= f) (b ≫= f)
  not a ≫= f = not (a ≫= f)

  _≫=≫_ : ∀ {I J K} → Sub J I → Sub K J → Sub K I
  (f ≫=≫ g) a = f a ≫= g
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
      → fib₁ I (coe₀ ret A) A
    coe-seq
      : ∀ {I J K A}
      → (f : Sub I J)
      → (g : Sub J K)
      → fib₁ K (coe₀ (g ≫=≫ f) A) (coe₀ g (coe₀ f A))
    coe-rel
      : ∀ {I J A}
      → {f g : Sub I J}
      → (φ : ∀ {𝒿} → rel (f 𝒿) (g 𝒿))
      → fib₁ J (coe₀ f A) (coe₀ g A)
open □Set public

-- FIXME
□_ : Symbols → □Set
fib₀ (□ I) J = Sub I J
fib₁ (□ I) J f g = ∀ {𝒿} → rel (f 𝒿) (g 𝒿)
coe₀ (□ I) = _≫=≫_
coe₁ (□ I) k p {𝓁} = {!!}
fib-idn (□ I) = rel-idn
fib-seq (□ I) p q {𝓁} = rel-seq (p {𝓁}) (q {𝓁})
fib-inv (□ I) p {𝓁} = rel-inv (p {𝓁})
coe-idn (□ I) = rel-idn
coe-seq (□ I) f g {𝒿} = {!!}
coe-rel (□ I) φ {ℓ} = {!!}
