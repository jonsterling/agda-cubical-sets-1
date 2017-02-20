# agda-cubical-sets

Cubical Set(oid)s in Agda

## Synopsis

This is a direct agda definition of the nominal presentation of cubical sets,
roughly following descriptions from Cohen, Coquand, Huber, Mortberg, and Pitts.

Because these are defined directly in Agda we use a representation similar to
families of setoids (as a flattened E-functor `Cat[Cubesᵒᵖ, Setoids]`). Another
difference is that our category of cubes uses a kind of defunctionalized
substitution for morphisms `Cubes[J, I]` rather than the function space `Set[I,
deMorgan(J)]`.

## Examples

We can define the interval in HIT style as follows:

```
data Interval (I : Sym) : Set where
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
…
```

Now we can reason about relatedness of the interval operators:

```
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
```