module Basis.Prelude.Function where

idn : {A : Set} → A → A
idn x = x

cmp : {A B C : Set} → (B → C) → (A → B) → (A → C)
cmp g f x = g (f x)
