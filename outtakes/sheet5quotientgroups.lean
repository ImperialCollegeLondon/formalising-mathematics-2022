/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import group_theory.subgroup.basic
/-!

# Quotient groups

-/

/-
subgroup.normal : Π {G : Type u_1} [_inst_1 : group G], subgroup G → Prop
-/

-- let G be a group and let N be a normal subgroup
variables {G : Type} [group G] (N : subgroup G) [hN : subgroup.normal N]

include hN

example (g h : G) (h1 : g ∈ N) : h * g * h⁻¹ ∈ N :=
begin
  apply hN.conj_mem,
  assumption,
end

-- The binary relation on G whose equivalence classes are the cosets of N
def R (a b : G) : Prop := a * b⁻¹ ∈ N 

variables (a b : G)

lemma R_def (a b : G) : R N a b ↔ a * b⁻¹ ∈ N := iff.rfl

lemma R_refl : reflexive (R N) :=
begin
  intro x,
  rw R_def,
  simp [N.one_mem],
end

lemma R_symm : symmetric (R N) :=
begin
  intros x y h,
  rw R_def at *,
  rw ← N.inv_mem_iff,
  simp [h],
end

lemma R_trans : transitive (R N) :=
begin
  intros x y z h1 h2,
  rw R_def at *,
  have h := N.mul_mem h1 h2,
  convert h using 1,
  group,
end

lemma R_equiv : equivalence (R N) :=
⟨R_refl N, R_symm N, R_trans N⟩

def s : setoid G :=
{ r := R N,
  iseqv := R_equiv N }

-- Q is quotient of G by N
notation `Q`:10000 N := quotient (s N)

-- things to do
-- (1) make Q a group
-- (2) Define group hom G -> Q
-- (3) prove universal property : if φ : G -> H is a group hom and N is in ker(φ)
--     then we get an induced map Q -> H

namespace quotient_group

def equiv_def (a b : G) : @has_equiv.equiv G (@setoid_has_equiv G (s N)) a b ↔ a * b⁻¹ ∈ N := iff.rfl
--  ↔ a * b⁻¹ ∈ N := sorry 
def one : Q N := quotient.mk' 1

def setoid_r_def (a b : G) : @setoid.r G (s N) a b ↔ a * b⁻¹ ∈ N := iff.rfl

instance : has_one (Q N) := ⟨one N⟩

def inv : (Q N) → Q N :=
quotient.map' (λ g, g⁻¹) begin
  intros a b h,
  dsimp, 
  rw equiv_def at *,
  rw [hN.mem_comm_iff, ← N.inv_mem_iff] at h,
  convert h using 1,
  group,
end

instance : has_inv (Q N) := ⟨inv N⟩

def mul : (Q N) → (Q N) → Q N :=
quotient.map₂' (λ g h, g * h) begin
  intros a b h1 c d h2,
  dsimp,
  rw equiv_def at *,
  rw (show (b * d)⁻¹ = d⁻¹ * b⁻¹, by group),
  rw hN.mem_comm_iff at h1,
  rw [mul_assoc, hN.mem_comm_iff],
  convert N.mul_mem h2 h1 using 1,
  group,
end

instance : has_mul (Q N) :=
⟨mul N⟩

instance group : group (Q N) :=
{ mul := (*),
  mul_assoc := begin
    intros a b c,
    apply quotient.induction_on₃' a b c, clear a b c,
    intros a b c,
    apply quotient.sound',
    dsimp,
    rw setoid_r_def,
    convert N.one_mem,
    group,
  end,
  one := 1,
  one_mul := begin
    intro a,
    apply quotient.induction_on' a, clear a,
    intro a,
    apply quotient.sound',
    dsimp,
    rw setoid_r_def,
    simp [N.one_mem],
  end,
  mul_one := begin
    intro a,
    apply quotient.induction_on' a, clear a,
    intro a,
    apply quotient.sound',
    dsimp,
    rw setoid_r_def,
    simp [N.one_mem],
  end,
  inv := has_inv.inv,
  mul_left_inv := begin
    intro a,
    apply quotient.induction_on' a, clear a,
    intro a,
    apply quotient.sound',
    dsimp,
    rw setoid_r_def,
    simp [N.one_mem],
  end, }

def canonical : G →* (Q N) :=
{ to_fun := quotient.mk',
  map_one' := rfl,
  map_mul' := λ x y, rfl }

-- (3) prove universal property : if φ : G -> H is a group hom and N is in ker(φ)
--     then we get an induced map Q -> H

variable {N}

def lift {H : Type} [group H] {φ : G →* H} (hφ : N ≤ φ.ker) :
(Q N) →* H :=
{ to_fun := λ q, quotient.lift_on' q φ begin
    clear q,
    intros a b h,
    rw setoid_r_def at h,
    have h2 : φ (a * b⁻¹) = 1,
    { rw ← monoid_hom.mem_ker,
      apply hφ h },
    rw φ.map_mul at h2,
    rw φ.map_inv at h2,
    exact mul_inv_eq_one.mp h2,
  end,
  map_one' := begin
     exact φ.map_one,
  end,
  map_mul' := begin intros x y,
    apply quotient.induction_on₂' x y, clear x y,
    exact φ.map_mul,
  end }

/-

G ----φ---> H
|        /
|mk    /
|    / lift
|   /
\//
Q
-/
example (H : Type) [group H] (g : G) (φ : G →* H) (hφ : N ≤ φ.ker) :
  φ g = lift hφ (quotient.mk' g) := rfl 

end quotient_group