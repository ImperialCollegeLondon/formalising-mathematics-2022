/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
/-!

# Subgroups

Let's go back to Lean's definition of a group instead of our own.
The reason for this is that Lean's groups API has many many lemmas
about groups (for example `)
-/

/-- `mysubgroup G` is the type of subgroups of a group `G`. -/
structure mysubgroup (G : Type) [group G] :=
(carrier : set G) -- `carrier` is the sub*set* of `G` which underlies the subgroup.
-- now the axioms for a subgroup
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

-- These axioms look a little ugly because they're constantly going on
-- about `carrier`: the subset corresponding to the subgroup. We'll fix
-- this in the 40 or so lines below.

-- Two subgroups are equal iff they have the same elements!
-- This lemma is proved in a "formulatic" way (it's true for
-- subgroups, subrings, subfields etc, with the same proof) 
-- and the wonderful people at mathlib central wrote some code which 
-- generates the proof automatically. You run it by tagging
-- `mysubgroup` with the `@[ext]` attribute:

attribute [ext] mysubgroup

-- we now have theorems my_subgroup.ext and my_subgroup.ext_iff

-- The next 30 lines are also boilerplate. You can skip them
namespace mysubgroup

-- let G be a group and let G be a subgroup
variables {G : Type} [group G] (H : mysubgroup G)

-- This line makes `g ∈ H` make sense; it says "`g ∈ H` is defined
-- to mean that `g` is in the underlying carrier set"
instance : has_mem G (mysubgroup G) :=
{ mem := λ m H, m ∈ H.carrier }

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
Say `H : subgroup G`, and `x` and `y` are terms of type `G` 
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
    rw ← inv_inv x,
    exact H.inv_mem h },
  { exact H.inv_mem },
end

-- We could prove a bunch more theorems here. Let's just do one more.
-- Let's show that if x and xy are in H then so is y.

theorem mul_mem_cancel_left {x y : G} (hx : x ∈ H) :
  x * y ∈ H ↔ y ∈ H :=
begin
  split,
  { intro h,
    suffices : x⁻¹ * x * y ∈ H,
      simpa,
    rw mul_assoc,
    exact H.mul_mem (H.inv_mem hx) h },
  { exact H.mul_mem hx },
end

theorem mul_mem_cancel_right {x y : G} (hx : x ∈ H) :
  y * x ∈ H ↔ y ∈ H :=
⟨λ hyx, begin
  suffices : y * x * x⁻¹ ∈ H,
    simpa,   
  exact H.mul_mem hyx (H.inv_mem hx),
  end, λ hy, H.mul_mem hy hx⟩

-- need : x ∈ A ∩ B defeq to x ∈ A ∧ x ∈ B

instance : has_le (mysubgroup G) :=
{ le := λ H₁ H₂, (H₁ : set G) ⊆ H₂ }

-- /-- The intersection of two subgroups is also a subgroup -/
-- def inf (H K : mysubgroup G) : mysubgroup G :=
-- { carrier := (H : set G) ∩ K,
--   one_mem' := 
--   begin
--     split,
--     { exact H.one_mem },
--     { exact K.one_mem },
--   end,
--   mul_mem' := 
--   begin
--     rintros x y ⟨hxH, hxK⟩ ⟨hyH, hyK⟩,
--     exact ⟨H.mul_mem hxH hyH, K.mul_mem hxK hyK⟩,
--   end,
--   inv_mem' :=
--   begin
--     rintros x ⟨hxH, hxK⟩,
--     exact ⟨H.inv_mem hxH, K.inv_mem hxK⟩,
--   end }

-- -- Notation for `inf` in computer science circles is ⊓ .

-- instance : has_inf (mysubgroup G) := ⟨inf⟩

-- /-- The underlying set of the inf of two subgroups is just their intersection -/
-- lemma inf_def (H K : mysubgroup G) : (H ⊓ K : set G) = (H : set G) ∩ K :=
-- begin
--   -- true by definition
--   refl
-- end

inductive in_closure (S : set G) : G → Prop
| of {x : G} (hx : x ∈ S) : in_closure x
| one : in_closure 1
| mul {x y : G} : in_closure x → in_closure y → in_closure (x * y)
| inv {x : G} : in_closure x → in_closure x⁻¹

def closure (S : set G) : mysubgroup G :=
{ carrier := {g | in_closure S g},
  one_mem' := in_closure.one,
  mul_mem' := λ _ _, in_closure.mul,
  inv_mem' := λ _, in_closure.inv }

--1) `subset_closure : S ⊆ closure S`
--2) `closure_mono : (S ⊆ T) → (closure S ⊆ closure T)`
--3) `closure_closure : closure (closure S) = closure S`

lemma subset_closure (S : set G) : S ⊆ closure S :=
begin
  intros g hgS,
  exact in_closure.of hgS,
end

lemma closure_induction_on {p : G → Prop} {S : set G} {x : G} (hx : x ∈ closure S)
  (hS : ∀ x ∈ S, p x)
  (h1 : p 1)
  (hmul : ∀ x y, p x → p y → p (x * y))
  (hinv : ∀ x, p x → p x⁻¹) : 
  -- conclusion after colon
  p x :=
begin
  induction hx with a h2 a b h5 h6 h7 h8 a h10 h11,
  { exact hS a h2 },
  { exact h1 },
  { exact hmul a b h7 h8 },
  { exact hinv a h11 },
end

lemma closure_mono {S T : set G} (hST : S ⊆ T) : 
  closure S ≤ closure T :=
begin
  intros x hxS,
  change x ∈ closure T,
  apply closure_induction_on hxS,
  { intros a haS,
    apply in_closure.of,
    exact hST haS },
  { exact (closure T).one_mem },
  { intros a b,
    exact (closure T).mul_mem },
  { intro a,
    exact (closure T).inv_mem }
end

lemma closure_closure {S : set G} :
  closure (closure S : set G) = closure S :=
begin
  ext x,
  split,
  { intro h,
    apply closure_induction_on h,
    { intros a ha,
      exact ha },
    { exact (closure S).one_mem },
    { intros _ _,
      exact (closure S).mul_mem },
    { intros _,
      exact (closure S).inv_mem } },
  { apply subset_closure }
end

lemma mem_closure_iff {S : set G} {x : G} : 
  x ∈ closure S ↔ ∀ H : mysubgroup G, S ⊆ H → x ∈ H :=
begin
  split,
  { intros hxS H hSH,
    apply closure_induction_on hxS,
    { apply hSH },
    { exact H.one_mem },
    { intros _ _,
      exact H.mul_mem },
    { intros _,
      exact H.inv_mem } },
  { intros IH,
    apply IH,
    exact subset_closure S }
end

lemma closure_le (S : set G) (H : mysubgroup G) : closure S ≤ H ↔ S ⊆ ↑H :=
begin
  split,
  { intros h g hgS,
    apply h,
    exact subset_closure S hgS },
  { rintros hSH a (haS : a ∈ closure S),
    rw mem_closure_iff at haS,
    exact haS _ hSH },
end

/- 
There is an underlying abstraction here, which you may not know about.
A "closure operator" in mathematics 

https://en.wikipedia.org/wiki/Closure_operator

is something mapping subsets of a set X to subsets of X, and satisfying three
axioms:

1) `subset_closure : S ⊆ closure S`
2) `closure_mono : (S ⊆ T) → (closure S ⊆ closure T)`
3) `closure_closure : closure (closure S) = closure S`

It works for closure in topological spaces, and it works here too.
It also works for algebraic closures of fields, and there are several
other places in mathematics where it shows up. This idea, of "abstracting"
and axiomatising a phenomenon which shows up in more than one place,
is really key in Lean.

Let's prove these three lemmas in the case where `X = G` and `closure S`
is the subgroup generated by `S`.

Here are some things you might find helpful.

Remember 
`mem_coe : g ∈ ↑H ↔ g ∈ H`
`mem_carrier : g ∈ H.carrier ↔ g ∈ H`

There's 
`mem_closure_iff : x ∈ closure S ↔ ∀ (H : subgroup G), S ⊆ ↑H → x ∈ H`
(`closure S` is a subgroup so you might need to use `mem_coe` or `mem_carrier` first)

For subsets there's
`subset.trans : X ⊆ Y → Y ⊆ Z → X ⊆ Z`

You might find `le_antisymm : H ≤ K → K ≤ H → H = K` from above useful
-/

-- This shows that every subgroup is the closure of something, namely its
-- underlying subset. 
lemma closure_self {H : mysubgroup G} : closure ↑H = H :=
begin
  ext x,
  split,
  { rintro (h : x ∈ closure (H : set G)),
    rw mem_closure_iff at h,
    apply h,
    refl },
  { apply subset_closure }
end

instance : preorder (mysubgroup G) :=
{ le := (≤),
  le_refl := λ H x hx, hx,
  le_trans := λ H₁ H₂ H₃ h1 h2 x hx, h2 $ h1 hx }

variable (G)
def gi : galois_insertion (closure : set G → mysubgroup G)
  (coe : mysubgroup G → set G) :=
{ choice := λ S _, closure S,
  gc := closure_le,
  le_l_u := λ H, subset_closure (H : set G),
  choice_eq := λ _ _, rfl }

instance : partial_order (mysubgroup G) :=
{ le_antisymm := begin
  intros H₁ H₂ h12 h21, 
  ext x,
  split,
  { apply h12, },
  { apply h21 },
end,
  .. mysubgroup.preorder }

instance : complete_lattice (mysubgroup G) :=
{.. galois_insertion.lift_complete_lattice (gi G)}

end mysubgroup
