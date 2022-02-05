/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ∪ A = A :=
begin
  ext x,
  split,
  { rintro (hA | hA);
    exact hA },
  { intro h,
    left,
    exact h },
end

example : A ∩ A = A :=
inter_self A -- found with `squeeze_simp`

example : A ∩ ∅ = ∅ :=
begin
  ext x,
  split,
  { rintro ⟨hx, ⟨⟩⟩ },
  { rintro ⟨⟩ },
end

example : A ∪ univ = univ :=
begin
  simp,
end

--set_option pp.notation false
example : A ⊆ B → B ⊆ A → A = B :=
begin
  -- library_search works
  intros hAB hBA,
  ext x,
  exact ⟨@hAB x, @hBA x⟩,
end

example : A ∩ B = B ∩ A :=
begin
  exact inter_comm A B, -- found with library_search
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  symmetry,
  exact inter_assoc A B C, -- I guessed the name!
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  ext x,
  split,
  { rintro (hA | hB | hC),
    { left, left, assumption },
    { left, right, assumption },
    { right, assumption }
  },  
  { rintro ((hA | hB) | hC),
    { left, assumption },
    { right, left, assumption },
    { right, right, assumption } }
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  exact union_distrib_left A B C, -- thanks library_search
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  exact inter_distrib_left A B C, -- guessed what this
  -- was called on basis of previous answer
end

