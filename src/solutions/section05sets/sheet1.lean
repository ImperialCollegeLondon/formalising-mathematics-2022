/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 1 : ∪ ∩ ⊆ and all that

Lean doesn't have "abstract" sets, it only has *subsets* of a type. If `X : Type` is a type
then the type of subsets of `X` is called `set X`. A term `A : set X`
can be thought of in three ways:

1) A set of elements of `X` (i.e. a set of elements all of which have type `X`);
2) A subset of `X`;
3) An element of the power set of `X`;
4) A function from `X` to `Prop` (sending the elements of `A` to `true` and the other ones to `false`)

So `set X` could have been called `subset X` or `powerset X`; I guess they chose `set X`
because it was the shortest.

Note that `X` is a type, but `A` is a term; the type of `A` is `set X`. This means
that `a : A` doesn't make sense. What we say instead is `a : X` and `a ∈ A`. 
Of course `a ∈ A` is a true-false statement, so `a ∈ A : Prop`. 

All the sets `A`, `B`, `C` etc we consider will be subsets of `X`. 
If `x : X` then `x` may or may not be an element of `A`, `B`, `C`,
but it will always be a term of type `X`.

-/

-- set up variables
variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D : set X) -- A,B,C are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

/-

# subset (`⊆`), union (`∪`) and intersection (`∩`)

Here are some mathematical facts:

`A ⊆ B` is equivalent to `∀ x, x ∈ A → x ∈ B`;
`x ∈ A ∪ B` is equivalent to `x ∈ A ∨ x ∈ B`;
`x ∈ A ∩ B` is equivalent to `x ∈ A ∧ x ∈ B`. 

All of these things are true *by definition* in Lean. Let's
check this.

-/

lemma subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B :=
begin
  -- ↔ is reflexive so `refl` works because LHS is defined to be equal to RHS
  refl
end

lemma mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
begin
  refl
end

lemma mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
iff.rfl -- you don't even have to go into tactic mode to prove this

/-

So now to change one side of these `↔`s to the other, you can
`rw` the appropriate lemma, or you can just use `change`. Or
you can ask yourself whether you need to do this at all.

Let's prove some theorems.

-/

example : A ⊆ A :=
begin
  rw subset_def, -- don't need this
  intro x,
  exact id, -- could do intro h, exact h
end

example : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  intros hAB hBC x hxA,
  apply hBC,
  apply hAB hxA, -- or apply hAB, exact hxA
end

example : A ⊆ A ∪ B :=
begin
  intros x hx,
  left,
  assumption,
end

example : A ∩ B ⊆ A :=
begin
  rintro x ⟨hxA, -⟩,
  exact hxA,
end

example : A ⊆ B → A ⊆ C → A ⊆ (B ∩ C) :=
begin
  intros hAB hAC x hxA,
  -- exact ⟨hAB hxA, hAC hxA⟩, -- finishes the level in one line
  split,
  { apply hAB,
    exact hxA },
  { exact hAC hxA },
end

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
begin
  rintros hBA hCA x (hxB | hxC),
  { exact hBA hxB },
  { exact hCA hxC }
end

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
begin
  exact set.union_subset_union, -- found this with `library_search`
end

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D :=
begin
  rintro hAB hCD x ⟨hxA, hxC⟩,
  exact ⟨hAB hxA, hCD hxC⟩,
end