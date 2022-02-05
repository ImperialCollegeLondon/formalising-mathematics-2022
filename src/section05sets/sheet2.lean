/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 2 : "the" empty set and the "universal set".

Lean notation for the empty subset of `X` is `∅`. Unlike in
set theory, there is more than one empty set in Lean! Every
type has an empty subset, and it *doesn't make sense*
to ask if `∅ : set ℕ` and `∅ : set ℤ` are equal, because
they have different types. 

At the other extreme, the subset of `X` containing all the terms of type `X`
is...well...mathematicians would just call it `X`, but `X` is a type not a subset. 
The subset of `X` consisting of every element of `X` is called `set.univ : set X`, 
or just `univ : set X` if we have opened the `set` namespace. Let's do that now.

-/

open set

/-

## Definition of ∅ and univ

`x ∈ ∅` is *by definition* equal to `false` and `x ∈ univ` is *by definition*
equal to `true`. You can use the `change` tactic to make these changes
if you like. But you don't have to. Remember that `triv` proves `true`
and `cases h` will solve a goal if `h : false`.

-/


-- set up variables
variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

open set

example : x ∈ (univ : set X) := 
begin
  sorry
end

example : x ∈ (∅ : set X) → false :=
begin
  sorry
end

example : A ⊆ univ :=
begin
  sorry
end

example : ∅ ⊆ A :=
begin
  sorry
end

