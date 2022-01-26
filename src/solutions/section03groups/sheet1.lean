/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Group theory in Lean

Lean has groups. But let's make our own anyway. In this sheet we will
learn about the `class` command, which is one of the ways to make
a theory of groups in Lean (and indeed the way it's done in `mathlib`)

We will also learn about `simp`, a tactic which does long series of
rewrites automatically. We'll even learn how to train it to solve a
certain kind of problem.

## Definition of a group

`group G` is already defined in `mathlib`, so let's define a new
type `mygroup G`. Here `G : Type` is a type, and `mygroup G` is the type of
group structures on `G`.

-/

/-- `mygroup G` is the type of group structures on the type `G`. -/
class mygroup (G : Type)
  extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(mul_one : ∀ a : G, a * 1 = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)
(mul_inv_self : ∀ a : G, a * a⁻¹ = 1)

/-

Right now the axioms are called `mygroup.mul_assoc`, `mygroup.one_mul` etc.
Furthermore we want to build some lemmas called things like `mygroup.one_inv`
and stuff. The fix? Let's move into the `mygroup` namespace, where they're
just caled `mul_assoc`, `one_inv` etc.

-/

namespace mygroup

-- tag all the axioms for groups with the `@[simp]` attribute.
-- Note that we can drop the `mygroup` prefix now as we're in the namespace.

attribute [simp] mul_assoc one_mul mul_one inv_mul_self mul_inv_self 

-- Throughout our work in this namespace, let `G` be a group and let
-- `a`, `b` and `c` be elements of `G`.
variables {G : Type} [mygroup G] (a b c : G)

/-

Five of the next seven lemmas are tagged with `@[simp]` as well.
See if you can prove all seven using (for the most part) the `rw` tactic.

-/

@[simp] lemma inv_mul_cancel_left : a⁻¹ * (a * b) = b :=
begin
  simp [← mul_assoc],
end

@[simp] lemma mul_inv_cancel_left : a * (a⁻¹ * b) = b :=
begin
  simp [← mul_assoc],
end

lemma left_inv_eq_right_inv {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : 
  b = c :=
begin
  have h : b * (a * c) = (b * a) * c := (mul_assoc b a c).symm, -- dot notation
  simpa [h2, h1] using h,
end

lemma mul_eq_one_iff_eq_inv : a * b = 1 ↔ a⁻¹ = b :=
⟨left_inv_eq_right_inv (inv_mul_self a), begin
  rintro rfl,
  simp 
end⟩

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  simp [← mul_eq_one_iff_eq_inv],
end

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a :=
begin
  simp [← mul_eq_one_iff_eq_inv],
end

@[simp] lemma mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := 
begin
  simp [← mul_eq_one_iff_eq_inv],
end

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? A theorem of Knuth
and Bendix says that we have just trained Lean's simplifier to prove
arbitrary true hypothesis-free identities in groups; those ten lemmas
we tagged with `@[simp]` are all you need. We've made a Noetherian
confluent rewrite system for group theory!

-/
-- example of Knuth-Bendix theorem
example (G : Type) [mygroup G] (a b : G) : 
  (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp

-- bonus puzzle : if g^2=1 for all g in G, then G is abelian
example (G : Type) [mygroup G] (h : ∀ g : G, g * g = 1) :
  ∀ g h : G, g * h = h * g :=
begin
  simp [mul_eq_one_iff_eq_inv] at h,
  intros a b,
  rw [← h (a * b)],
  rw mul_inv_rev,
  simp [h],
end

end mygroup
