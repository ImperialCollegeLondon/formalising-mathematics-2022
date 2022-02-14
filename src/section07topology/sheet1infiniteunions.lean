/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Infinite unions and intersections

If `X : Type` and `A B : set X` are subsets of `X`, then we've
seen that Lean understands the notation `A ∪ B`. Furthermore,
if `x : X` is a term of type `X` then `x ∈ A ∪ B` is
definitionally equal to `x ∈ A ∨ x ∈ B`, and `x ∈ A ∩ B` is
definitionally `x ∈ A ∧ x ∈ B`.

But what about infinite unions and intersections? Turns out
that there are *three* ways to do them in Lean, all with
slightly different notations. There are also ways to switch
between these things.

## `Union` : indexed union over a type.

Say `A₀, A₁, A₂, ...` are infinitely many subsets of `X`.
In Lean we would model this as `A : ℕ → set X`, a function
from the naturals to subsets of `X` sending `i` to `Aᵢ`.
More generally we could have an arbitrary "index type" `ι : Type`
(that's an "iota", the notation typically used for index types)
and a function `A : ι → set X`, corresponding to subsets `Aᵢ` of `X`
as `i` varies through `ι`.  

The way to take the union of these sets is `set.Union A` (note the capital U;
small u means union of two things, capital means union of arbitrary
number of things). But you should use the notation for this function,
which is `⋃ (i : ι), A i`. Here is some code and a couple of examples
for you to try.

-/

section Union

-- Let `Aᵢ` for `i : ι` be a collection of subsets of `X`
variables (X : Type) (ι : Type) (A : ι → set X)

-- The union of the Aᵢ

example : set X := ⋃ (i : ι), A i

example : set.Union A = ⋃ (i : ι), A i :=
begin
  -- RHS is notation for LHS; in fact they're syntactically equal
  refl
end

-- A term `x : X` is in the Union if and only if it's in one of the `Aᵢ`

-- The below lemma is not `refl`. It's `set.mem_Union`.

example (x : X) : (x ∈ ⋃ (i : ι), A i) ↔ ∃ i : ι, x ∈ A i :=
begin
  exact set.mem_Union,
end

-- Of course mem_Union is very useful for rewriting, even though it's
-- definitional.

-- You can take the union over more than index type,
-- if have sets `Bᵢₖ` indexed by two variables.

example (ι κ : Type) (B : ι → κ → set X) : set X :=
⋃ (i : ι) (k : κ), B i k

-- This is just implemented as a Union of a Union (just like
-- `∀ a n : ℕ, ...` is internally `∀ a : ℕ, ∀ b : ℕ, ...`)

example (ι κ : Type) (B : ι → κ → set X) :
  (⋃ (i : ι) (k : κ), B i k) = ⋃ (i : ι), ⋃ (k : κ), B i k :=
begin
  -- note that they're actually syntactically equal
  refl
end

/-

## Inter : indexed intersection over a type

Here's the story for the intersection: It's called Inter,
it has all the same syntax.

-/

example : set X := ⋂ (i : ι), A i 

example (x : X) : (x ∈ ⋂ (i : ι), A i) ↔ ∀ i : ι, x ∈ A i :=
begin
  exact set.mem_Inter, -- also not `refl`.
end

-- Now try these exercises. 

variable (Y : Type)

example (F : ι → set X) (f : X → Y) :
  f '' (⋃ (i : ι), F i) = ⋃ (i : ι), f '' (F i) :=
begin
  -- Try a proof from first principles starting with `ext y`
  -- Also try `library_search`.
  sorry
end

example (G : ι → set Y) (f : X → Y) :
  f ⁻¹' (⋃ (i : ι), G i) = ⋃ (i : ι), f ⁻¹' (G i) :=
begin
  -- If you tried `library_search` last time, try
  -- guessing the name of the theorem this time
  sorry
end

example (G : ι → set Y) (f : X → Y) :
  f ⁻¹' (⋂ (i : ι), G i) = ⋂ (i : ι), f ⁻¹' (G i) :=
begin
  -- If you don't want to do it, can you guess the name?
  sorry
end

-- What do you think about `set.image_Inter` by the way?
-- Try stating what it should say. Is it true?

-- NB note the brackets around the LHS; Lean seems to
-- eat the equality and keep eating when trying to figure
-- out the ⋃ notation otherwise

-- Here's a couple more for you to try
example (S : set X) : (⋃ i, A i) ⊆ S ↔ (∀ i, A i ⊆ S) :=
begin
  sorry
end

example (κ : Type) (B : ι → κ → set X) :
  (⋃ (i : ι) (k : κ), B i k) = ⋃ (k : κ) (i : ι), B i k :=
begin
  sorry,
end

-- Feel free to make some up yourselves if you want abstract practice;
-- however you might just want to get to the topology.

end Union

/-

## `bUnion` : union of indexed sets satisfying a condition

What if we still have our family of sets `A₀`, `A₁`, `A₂` indexed over the
naturals, but we want to only take the union over the `Aᵢ` with `i` even,
or with `i` prime? More generally, what if we have `A : ι → set X` and some
subset `S : set ι` and we want to take the union of `Aᵢ` for `i ∈ S`?

Lean calls this concept `set.bUnion`. The actual definition `set.bUnion`
doesn't exist, but the lemmas about it all have this name.

-/

section bUnion

-- Let `Aᵢ` for `i : ι` be a collection of subsets of `X`
variables (X : Type) (ι : Type) (A : ι → set X) (S : set ι)

-- The union of the Aᵢ for which P(i) is true

example : set X := ⋃ (i ∈ S), A i

-- here's what the notation expands to
example : (⋃ (i ∈ S), A i) = ⋃ (i : ι) (h : i ∈ S), A i := rfl 

-- So get this; it's taking a union over all i of a union over all proofs
-- that `i ∈ S` of Aᵢ. This works! If `i : ι` then if you take the
-- union over all proofs that `i ∈ S` of `A i` then either there's no
-- proofs (because it's false) and the union is empty, or there's
-- at least one proof (because it's true) and so you get `A i`. Now
-- take the union over all `i` and it works!

-- A term `x : X` is in the sUnion if and only if it's in one of the
-- elements of S

-- The below lemma can be proved with `refl`. It's `set.mem_sUnion`
-- (even if it's true by definition, having name is useful for rewriting)

example (x : X) : x ∈ (⋃ (i ∈ S), A i) ↔ ∃ (i : ι) (h : i ∈ S), x ∈ A i :=
begin
  -- not refl
  exact set.mem_bUnion_iff, -- it's slightly sad that mem_bUnion
  -- is only one implication and mem_bUnion_iff is the iff statement.
  -- This isn't like the mem_Union situation.
end

/-

## bInter : indexed intersection over a subset of an index set.

Here's the story:

-/

example : set X := ⋂ (i ∈ S), A i

example (x : X) : x ∈ (⋂ (i ∈ S), A i) ↔ ∀ (i : ι) (h : i ∈ S), x ∈ A i :=
begin
  -- not refl
  exact set.mem_bInter_iff,
end

-- Some exercises

variable (Y : Type)

example (f : X → Y) :
  f '' (⋃ (i ∈ S), A i) = ⋃ (i ∈ S), f '' (A i) :=
begin
  -- If you can guess what it's called you don't need to prove it ;-)
  sorry
end

example (B : ι → set Y) (f : X → Y) :
  f ⁻¹' (⋂ (i ∈ S), B i) = ⋂ (i ∈ S), f ⁻¹' (B i) :=
begin
  sorry
end

end bUnion

/-

## sUnion : union of a set of subsets

Sometimes we don't have a natural indexing type to take an arbitrary union
over; for example the interior of a subset `A` of a topological space is the
union of the open sets contained in `A`.

So here the setup is we have `S : set (set X)`, i.e. a collection of
subsets of `X` (like the open sets in a topology for example),
and we want to take the union of these sets. This union is `set.sUnion S`,
and it has notation `⋃₀`. More precisely:
-/

section sUnion

-- Let `S` be a set of subsets of `X`
variables (X : Type) (S : set (set X))

-- The union of the elements of S
example : set X := ⋃₀ S

example : set.sUnion S = ⋃₀ S :=
begin
  -- RHS is notation for LHS; in fact they're syntactically equal
  refl
end

-- A term `x : X` is in the sUnion if and only if it's in one of the
-- elements of S

-- The below lemma can be proved with `refl`. It's `set.mem_sUnion`
-- (even if it's true by definition, having name is useful for rewriting)

example (x : X) : (x ∈ ⋃₀ S) ↔ ∃ s ∈ S, x ∈ s :=
begin
  exact set.mem_sUnion, -- this 
end

-- In fact sUnion is a special case of bUnion, where the index set is `set X`. 
example : (⋃₀ S) = ⋃ (s ∈ S), s :=
begin
  exact set.sUnion_eq_bUnion
end

/-

## sInter : intersection of a set of sets

Here's the story:

-/

example : set X := ⋂₀ S

example : set.sInter S = ⋂₀ S :=
begin
  -- RHS is notation for LHS; in fact they're syntactically equal
  refl
end

-- A term `x : X` is in the sInter if and only if it's in all of the
-- elements of S. Can be proved with `refl`. It's `set.mem_sInter`

example (x : X) : (x ∈ ⋂₀ S) ↔ ∀ s ∈ S, x ∈ s :=
begin
  exact set.mem_sInter, -- this is definitional
end

-- Some exercises

variable (Y : Type)

example (S : set (set X)) (f : X → Y) :
  f '' (⋃₀ S) = ⋃₀ ((set.image f) '' S) :=
begin
  -- This should be set.image_sUnion but it doesn't seem to be there?
  sorry
end

example (S : set (set X)) (U : set X) (hU : U ∈ S) : 
  ⋂₀ S ⊆ U :=
begin
  -- If you don't want to do it, can you guess the name?
  sorry
end

end sUnion
