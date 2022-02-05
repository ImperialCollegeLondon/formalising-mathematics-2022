/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- the reals

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : set X` of `X` we can push it
forward to make a subset `f(S) : set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`. 

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `set X`. 
In Lean we use the notation `f '' S` for this. This is notation
for `set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : set Y` of `Y` we can
pull it back to make a subset `f⁻¹(T) : set X` of `X`. The definition
of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `has_inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type. The notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variables (X Y : Type) (f : X → Y) (S : set X) (T : set Y)

example : S ⊆ f ⁻¹' (f '' S) :=
begin
  intros x hx,
  exact ⟨x, hx, rfl⟩, -- use x, etc etc also works
end

example : f '' (f ⁻¹' T) ⊆ T :=
begin
  rintros - ⟨x, hx, rfl⟩,
  exact hx,
end

theorem gc : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T :=
begin
  split,
  { intros h x hxS,
    refine h ⟨x, hxS, rfl⟩ },
  { rintro h - ⟨x, hx, rfl⟩,
    refine h hx }
end

-- image and preimage form a Galois connection
-- look up Galois connections in the mathlib docs to learn about what these are
-- right click on `galois_connection` or do `unfold galois_connection` to 
-- find out what this question's asking
-- NB `≤` on subsets is defined to be `⊆` 
example : galois_connection (λ S, f '' S) (λ T, f ⁻¹' T) :=
begin
  apply gc,
end