/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
-- the next import will be enough for this sheet
import topology.basic

/-!

# Topology : making the API for `interior`.

(I'll assume you know the mathematics behind the interior of a subset of a topological space
in this sheet). 

The way to make a type `X` into a topological space is to 
tell the type class inference system that you'd like it to
keep track of a topological space structure on `X`. So it's

`variables (X : Type) [topological_space X]`

Lean has interiors of topological spaces, but let's
make our own, as warm-up.

-/

-- Here's the notation we'll use in this sheet
variables {X : Type} [topological_space X] (S : set X)

/-

## The API for topological spaces

`is_open S : Prop` is the predicate that `S : set X` is open.

Now here's some standard facts from topology. I'll tell you the names
of the proofs, you can guess what they're proofs of
(and then check with `#check`, which tells you the type of a term, so
if you give it a theorem proof it will tell you the theorem statement). 

* is_open_univ
* is_open_Union, is_open_bUnion, is_open_sUnion (note the capital U)
* is_open.inter (note the small i) (and the dot to enable dot notation)

-/

/-

## Interiors

Lean has interior of a set, but let's make them ourselves
because it's a nice exercise.

-/

-- Got to call it `interior'` with a dash, because Lean already has `interior`
-- The following would work for the definition -- a "bUnion".
def interior' (S : set X) : set X := ⋃ (U ∈ {V : set X | is_open V ∧ V ⊆ S}), U

-- useful for rewrites; saves you having to unfold `interior'` (a good Lean
-- proof should never use `unfold` unless you're making API).
lemma mem_interior' (x : X) : x ∈ interior' S ↔ ∃ (U : set X) (hU : is_open U) (hUS : U ⊆ S), x ∈ U :=
begin
  unfold interior',
  rw set.mem_bUnion_iff,
  finish,
end



/-
Two alternative definitions: a Union of a Union, Union of a Union of a Union, or a sUnion.

-- Union of Union
def interior'' (S : set X) : set X := ⋃ (U : set X) (h : is_open U ∧ U ⊆ S), U

-- Union of Union of Union
def interior'' (S : set X) : set X := ⋃ (U : set X) (hU : is_open U) (hUS : U ⊆ S), U

-- sUnion
def interior''' (S : set X) : set X := ⋃₀ ({V : set X | is_open V ∧ V ⊆ S})

You can try one of those if you'd rather. Then in the above proof you might end up
rewriting set.mem_Union_iff or set.mem_sUnion_iff.
-/

-- Lean has `is_open_Union` and `is_open_bUnion` and `is_open_sUnion`.
-- Because our definition is a `bUnion`, we could start with `apply is_open_bUnion`,
-- the "correct form" of the assertion that an arbitrary 

lemma interior'_open : is_open (interior' S) := 
begin
  apply is_open_bUnion,
  rintro U ⟨hU, h⟩,
  exact hU,
end

lemma interior'_subset : interior' S ⊆ S :=
begin
  intros x hx,
  rw mem_interior' at hx,
  rcases hx with ⟨U, hU, hUS, h⟩,
  exact hUS h,
end

-- Lean can work out S from hUS so let's make S a {} input for this one

variable {S}

lemma subset_interior' {U : set X} (hU : is_open U) (hUS : U ⊆ S) : U ⊆ interior' S :=
begin
  intros x hx,
  rw mem_interior',
  exact ⟨U, hU, hUS, hx⟩,
end


-- Similarly here I put S and T in squiggly brackets because Lean can figure them out
-- when it sees hST
lemma interior'_mono {S T : set X} (hST : S ⊆ T) : interior' S ⊆ interior' T :=
begin
  intros x hx,
  rw mem_interior' at *,
  rcases hx with ⟨U, hU, hUS, hxU⟩,
  exact ⟨U, hU, hUS.trans hST, hxU⟩,
end

-- instead of starting this with `ext`, you could `apply set.subset.antisymm`,
-- which is the statement that if S ⊆ T and T ⊆ S then S = T.
lemma interior'_interior' : interior' (interior' S) = interior' S :=
begin
  apply set.subset.antisymm,
  { exact interior'_mono (interior'_subset S) },
  { exact subset_interior' (interior'_open S) rfl.subset },
end

-- Some examples of interiors
lemma interior'_empty : interior' (∅ : set X) = ∅ :=
begin
  ext y,
  simp,
  exact @interior'_subset _ _ ∅ _,
end

lemma interior'_univ : interior' (set.univ : set X) = set.univ :=
begin
  ext y,
  simp,
  rw mem_interior',
  refine ⟨set.univ, is_open_univ, rfl.subset, by triv⟩,
end

lemma interior'_inter (S T : set X) : interior' (S ∩ T) = interior' S ∩ interior' T :=
begin
  apply set.subset.antisymm,
  { refine set.subset_inter (interior'_mono (set.inter_subset_left _ _)) 
      (interior'_mono (set.inter_subset_right _ _)) },
  { rintro x ⟨hxS, hxT⟩,
    rw mem_interior' at *,
    rcases hxS with ⟨U, hU, hUS, hxU⟩,
    rcases hxT with ⟨V, hV, hVT, hxV⟩,
    refine ⟨U ∩ V, hU.inter hV, set.inter_subset_inter hUS hVT, hxU, hxV⟩,
  },
end
