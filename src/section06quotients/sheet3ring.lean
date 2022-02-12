/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import section06quotients.sheet2zmod37

/-!

# Z/37 is a ring

-/

namespace Zmod

-- We already defined negation. Let's set up notation for it.

instance : has_neg Zmod37 :=
{ neg := neg }

-- Let's train the simplifier to push everything into
-- the brackets
@[simp] lemma neg_def (a : ℤ) : -⟦a⟧ = ⟦-a⟧ :=
begin
  refl
end

-- and notation for zero
instance : has_zero Zmod37 :=
{ zero := ⟦0⟧ }

@[simp] lemma zero_def : (0 : Zmod37) = ⟦0⟧ :=
begin
  refl
end

-- Finally addition. This is a map `Zmod37 → Zmod37 → Zmod37` so we 
-- can use a function in the library called `quotient.map₂` to descend
-- addition on the integers; we will need to prove a result saying
-- it's well-defined though.

def add : Zmod37 → Zmod37 → Zmod37 :=
quotient.map₂ (λ a b, a + b) begin
  -- keep introsing, and dsimp the lambdas away
  rintros a b ⟨c, hc⟩ d e ⟨f, hf⟩,
  refine ⟨c + f, _⟩,
  dsimp,
  rw [mul_add, ←hc, ←hf],
  ring,
end

instance : has_add Zmod37 :=
{ add := add }

@[simp] lemma add_def (a b : ℤ) : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ :=
begin
  refl
end

lemma add_zero (z : Zmod37) : z + 0 = z :=
begin
  apply quotient.induction_on z, clear z,
  intro a,
  simp,
end

lemma add_comm (y z : Zmod37) : y + z = z + y :=
begin
  apply quotient.induction_on₂ y z, clear y z,
  intros,
  simp,
  use 0,
  ring,
end

instance add_comm_group : add_comm_group Zmod37 :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_assoc := begin     intros a b c,
    apply quotient.induction_on₃ a b c,
    clear a b c,
    intros a b c,
    simp,
    use 0,
    ring, end,
  zero_add := begin     intro a,
    apply quotient.induction_on a,
    clear a,
    intro a,
    simp, end,
  add_zero := add_zero,
  add_left_neg := begin     intro a,
    apply quotient.induction_on a,
    clear a,
    intro a,
    simp, end,
  add_comm := add_comm }

-- Think you can make it a ring?

instance : has_one Zmod37 :=
{ one := ⟦1⟧ }

@[simp] lemma one_def : (1 : Zmod37) = ⟦1⟧ :=
begin
  refl
end

def mul : Zmod37 → Zmod37 → Zmod37 :=
quotient.map₂ (λ x y, x * y) begin
  rintros a b ⟨c, hc⟩ d e ⟨f, hf⟩,
  dsimp only,
  -- a = b + 37 * c
  -- d = e + 37 * f
  use f * b + c * d,
  rw mul_add,
  rw ← mul_assoc,
  rw ← hf,
  rw ← mul_assoc,
  rw ← hc,
  ring,
end

instance : has_mul Zmod37 :=
{ mul := mul }

@[simp] lemma mul_def (a b : ℤ) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ :=
begin
  refl
end

instance : comm_ring Zmod37 :=
{ 
  mul := (*),
  add := (+),
  mul_assoc := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    clear a b c,
    intros a b c,
    simp,
    use 0,
    ring,
  end,
  one := 1,
  one_mul := begin
    intro a,
    apply quotient.induction_on a,
    clear a,
    intro a,
    simp,
  end,
  mul_one := begin
    intro a,
    apply quotient.induction_on a,
    clear a,
    intro a,
    simp,
  end,
  left_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    clear a b c,
    intros a b c,
    simp,
    use 0,
    ring,
  end,
  right_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    clear a b c,
    intros a b c,
    simp,
    use 0,
    ring,
  end,
  mul_comm := begin
    intros y z,
    apply quotient.induction_on₂ y z, clear y z,
    intros,
    simp,
    use 0,
    ring,
end,
  ..Zmod.add_comm_group }
end Zmod
