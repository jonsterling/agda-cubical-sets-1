module Prelude where

open import Agda.Builtin.Bool public
open import Agda.Builtin.String public

module T where
  infix 0 ¬_

  data 𝟘 : Set where

  ¬_ : ∀ {a} → Set a → Set a
  ¬ A = A → 𝟘

  absurd : {A : Set} → A → ¬ ¬ A
  absurd a k = k a

  record 𝟙 : Set where
    constructor *

  instance
    trivial : 𝟙
    trivial = *

  record _⊗_ (A B : Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B
  open _⊗_ public

  data _⊕_ (A B : Set) : Set where
    inl : (a : A) → A ⊕ B
    inr : (b : B) → A ⊕ B

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _▸_
    field
      fst : A
      snd : B fst
  open Σ public

  syntax Σ A (λ x → B) = Σ[ A ∋ x ] B
open T public
  using (¬_)
  using (*)
  using (_,_)
  using (_▸_)

module ≡ where
  open import Agda.Builtin.Equality public

  infix 4 _≢_

  _≢_ : ∀ {a} {A : Set a} (x : A) → A → Set a
  x ≢ y = ¬ (x ≡ y)

  seq : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  seq p refl = p

  inv : {A : Set} {a b : A} → a ≡ b → b ≡ a
  inv refl = refl

  subst : ∀ {A : Set} {x y} (Ψ : A → Set) (ρ : x ≡ y) → Ψ x → Ψ y
  subst Ψ refl x = x

  ap : ∀ {A B : Set} {x₀ x₁} (f : A → B) → x₀ ≡ x₁ → f x₀ ≡ f x₁
  ap f refl = refl

  ap² : ∀ {A B C : Set} {x₀ x₁ y₀ y₁} (f : A → B → C) → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
  ap² f refl refl = refl
open ≡ public
  using (_≡_)
  using (refl)

data Decidable (A : Set) : Set where
  no : (A → T.𝟘) → Decidable A
  yes : A → Decidable A

module List where
  open import Agda.Builtin.List public
open List public
  hiding (module List)

module Maybe where
  data Maybe (A : Set) : Set where
    none : Maybe A
    some : A → Maybe A

  _≫=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  none ≫= f = none
  some x ≫= f = f x

  some-inj : {A : Set} {x y : A} → some x ≡ some y → x ≡ y
  some-inj refl = refl

  none≢some : {A R : Set} {a : A} → none ≡ some a → R
  none≢some ()
open Maybe public
  hiding (module Maybe)
  using (Maybe)
  using (none)
  using (some)

module Nat where
  open import Agda.Builtin.Nat public
    renaming (suc to succ)

  _≟_ : (n₀ n₁ : Nat) → Decidable (n₀ ≡ n₁)
  zero ≟ zero = yes refl
  zero ≟ succ _ = no λ()
  succ _ ≟ zero = no λ()
  succ n₀ ≟ succ n₁ with n₀ ≟ n₁
  … | no n₀≢n₁ = no λ { refl → n₀≢n₁ refl }
  … | yes refl = yes refl
open Nat public
  hiding (module Nat)
  using (Nat)
  using (zero)
  using (succ)
  using (_+_)
  using (_-_)

module String where
  open import Agda.Builtin.String public

  private
    primitive
      primTrustMe : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y

  _≟_ : (s₀ s₁ : String) → Decidable (s₀ ≡ s₁)
  s₀ ≟ s₁ with primStringEquality s₀ s₁
  … | false = no void where postulate void : _
  … | true = yes primTrustMe

record Inspect {A : Set} {B : A → Set} (f : (a : A) → B a) (a : A) (b : B a) : Set where
  constructor [_]?
  field
    φ : f a ≡ b

inspect : {A : Set} {B : A → Set} (f : (a : A) → B a) (a : A) → Inspect f a (f a)
inspect f a = [ refl ]?
