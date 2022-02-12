/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Making ℤ from ℕ²

You can define `ℤ` as ℕ² / ≈, where (a,b) ≈ (c,d) ↔ a + d = b + c.
This sheet goes through this (definition, commutative ring structure) with very few hints.
All the techniques are things we've seen in the earlier sheets.

Hint: if the tactic state is

h : a + d = b + c
⊢ c + b = d + a

you can close the goal with `linarith`. If things get nonlinear (multiplication,
I'm looking at you), there's always `nlinarith`.

-/

/-

# Warm-up: how products work in Lean

-/

-- constructor for ℕ × ℕ 

example : ℕ × ℕ := (3,4)

-- eliminators

def foo : ℕ × ℕ := (37, 53)

example : foo.1 = 37 := 
begin
  refl
end

example : foo.2 = 53 := 
begin
  refl
end

-- warning : constructor on eliminators isn't refl
example (a : ℕ × ℕ) : a = (a.1, a.2) :=
begin
  -- refl fails
  cases a with x y, -- a term of type ℕ × ℕ is a pair; `cases` takes it apart.
  -- now refl works
  refl,
end

def R (ab cd : ℕ × ℕ) : Prop :=
ab.1 + cd.2 = ab.2 + cd.1

lemma R_def (ab cd : ℕ × ℕ) :
R ab cd ↔ ab.1 + cd.2 = ab.2 + cd.1 := 
begin
  sorry
end

lemma R_def' (a b c d : ℕ) :
R (a, b) (c, d) ↔ a + d = b + c :=
begin
  sorry
end 


lemma R_refl : reflexive R :=
begin
  sorry,
end

lemma R_symm : symmetric R :=
begin
  sorry,
end

lemma R_trans : transitive R :=
begin
  sorry,
end

instance s : setoid (ℕ × ℕ) :=
{ r := R,
  iseqv := ⟨R_refl, R_symm, R_trans⟩ }

@[simp] lemma equiv_def (a b c d : ℕ) :
  (a, b) ≈ (c, d) ↔ a + d = b + c :=
begin
  sorry
end

notation `myint` := quotient s

-- Amusingly, we can't now make a myint namespace unless
-- we do some weird quote thing (Lean unfolds the notation otherwise)
namespace «myint»

instance : has_zero myint :=
{ zero := ⟦(0,0)⟧ }

@[simp] lemma zero_def : (0 : myint) = ⟦(0, 0)⟧ :=
begin
  sorry
end

def neg : myint → myint :=
quotient.map (λ ab, (ab.2, ab.1)) begin
  sorry,
end

instance : has_neg myint :=
{ neg := neg }

@[simp] lemma neg_def (a b : ℕ) : 
  -⟦(a, b)⟧ = ⟦(b, a)⟧ :=
begin
  sorry,
end

def add : myint → myint → myint :=
quotient.map₂ (λ ab cd, (ab.1 + cd.1, ab.2 + cd.2)) begin
  sorry,
end

instance : has_add myint :=
{ add := add }

@[simp] lemma add_def (a b c d : ℕ) :
  ⟦(a, b)⟧ + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ :=
begin
  sorry
end

instance add_comm_group : add_comm_group myint :=
{ add := (+),
  add_assoc := begin
    sorry,
  end,
  zero := 0,
  zero_add := begin
    sorry,
  end,
  add_zero := begin
    sorry,
  end,
  neg := has_neg.neg,
  add_left_neg := begin
    sorry,
  end,
  add_comm := begin
    sorry,
  end }

-- our model is that the equivalence class ⟦(a, b)⟧
-- represents the integer a - b
instance : has_one myint :=
{ one := ⟦(1, 0)⟧}

@[simp] lemma one_def : (1 : myint) = ⟦(1, 0)⟧ :=
begin
  sorry,
end

-- (a-b)*(c-d)=(ac+bd)-(ad+bc)
def mul : myint → myint → myint :=
quotient.map₂ (λ ab cd, (ab.1 * cd.1 + ab.2 * cd.2, ab.1 * cd.2 + ab.2 * cd.1)) begin
  sorry,
end

instance : has_mul myint :=
{ mul := mul }

@[simp] lemma mul_def (a b c d : ℕ) :
  ⟦(a, b)⟧ * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ :=
begin
  sorry,
end

instance : comm_ring myint :=
{ add := (+),
  zero := 0,
  mul := (*),
  mul_assoc := begin
    sorry,
  end,
  one := 1,
  one_mul := begin
    sorry,
  end,
  mul_one := begin
    sorry,
  end,
  left_distrib := begin
    sorry,
  end,
  right_distrib := begin
    sorry,
  end,
  mul_comm := begin
    sorry,
  end,
  ..myint.add_comm_group }

end «myint»

