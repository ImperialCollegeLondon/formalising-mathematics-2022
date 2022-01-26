/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
/-!

# Subgroups

[note: the questions start on line 125 or so! ]

Let's go back to Lean's definition of a group instead of our own.
The reason for this is that Lean's groups API has many many lemmas
about groups.

Let's define our own subgroups though. We start with all the basic
API needed to even get going.

What you need to know: `set G` is the type of subsets of `G`. 
A subgroup of G is a subset of G which is closed under the group
structure (i.e. contains `1` and is closed under `*` and `⁻¹` ).
Here's how we say this in Lean
-/

/-- `mysubgroup G` is the type of subgroups of a group `G`. -/
structure mysubgroup (G : Type) [group G] :=
(carrier : set G) -- `carrier` is the sub*set* of `G` which underlies the subgroup.
-- now the axioms for a subgroup
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

/-

These axioms look a little ugly because they're constantly going on
about `carrier`: the subset corresponding to the subgroup. We'll fix
this in the 40 or so lines below. You don't have to worry about these;
this is all the set-up you need to make the definition usable and make
notation like `g ∈ H` work for `H : mysubgroup G`.

## Extensionality

Two subgroups are equal iff they have the same elements!
This lemma is proved in a "formulatic" way (it's true for
subgroups, subrings, subfields etc, with the same proof) 
and the wonderful people at mathlib central wrote some code which 
generates the proof automatically. You run it by tagging
`mysubgroup` with the `@[ext]` attribute:

-/

attribute [ext] mysubgroup

-- we now have theorems `my_subgroup.ext` and `my_subgroup.ext_iff`,
-- plus the `ext` tactic works on subgroups and reduces goals of
-- the form `H₁ = H₂` to `∀ g, g ∈ H₁ ↔ g ∈ H₂`  

-- The next 30 lines are also boilerplate. You can skip them
namespace mysubgroup

-- let G be a group and let G be a subgroup
variables {G : Type} [group G] (H : mysubgroup G)

variables (a b c : G)

-- This line makes `g ∈ H` make sense; it says "`g ∈ H` is defined
-- to mean that `g` is in the underlying carrier set"
instance : has_mem G (mysubgroup G) :=
{ mem := λ a H, a ∈ H.carrier }

-- This line means that if `H : subgroup G` and the user suddenly starts
-- talking about `H : set G` without warning, then this just means
-- `H.carrier` again -- the underlying set.
instance : has_coe (mysubgroup G) (set G) := 
{ coe := λ H, H.carrier }

/-- `g` is in `H` considered as a subset of `G`, iff `g` is in `H` considered
as subgroup of `G`. -/
@[simp] lemma mem_coe {g : G} : g ∈ (H : set G) ↔ g ∈ H :=
begin
  -- These two concepts just mean the same thing
  refl
end

-- We now start reformulating the axioms without ever mentioning "carrier".
theorem one_mem : (1 : G) ∈ H :=
begin
  apply H.one_mem',
end

/-- A subgroup is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
begin
  apply H.mul_mem',
end

/-- A subgroup is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
begin
  apply H.inv_mem',
end

/-

Basic boilerplate code is now over.

So here are the three theorems which you need to remember about subgroups.
Say `H : mysubgroup G`, and `x` and `y` are terms of type `G` 
(i.e. elements of `G`). Then

`H.one_mem : (1 : G) ∈ H`
`H.mul_mem : x ∈ H → y ∈ H → x * y ∈ H`
`H.inv_mem : x ∈ H → x⁻¹ ∈ H`

These now look like the way a mathematician would write things.

Now let's start to prove basic theorems about subgroups (or, as a the computer
scientists would say, make a basic _interface_ or _API_ for subgroups),
using this sensible notation.

Here's an example; let's prove `x ∈ H ↔ x⁻¹ ∈ H`. Let's put the more
complicated expression on the left hand side of the `↔` though, because then
we can make it a `simp` lemma.

-/

@[simp] theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H := 
begin
  split,
  { intro h,
    convert H.inv_mem h,
    rw inv_inv }, -- found using `squeeze_simp`
  { exact H.inv_mem }
end

-- We could prove a bunch more theorems here. Let's just do two more.

theorem mul_mem_cancel_left {x y : G} (hx : x ∈ H) :
  x * y ∈ H ↔ y ∈ H :=
begin
  split,
  { intro hxy,
    have hxi := H.inv_mem hx,
    have h := H.mul_mem hxi hxy,
    simpa using h },
  { exact H.mul_mem hx }
end

theorem mul_mem_cancel_right {x y : G} (hx : x ∈ H) :
  y * x ∈ H ↔ y ∈ H :=
begin
  split,
  { replace hx := H.inv_mem hx,
    intro h,
    convert H.mul_mem h hx,
    simp },
  { intro hy,
    exact H.mul_mem hy hx }
end

end mysubgroup
