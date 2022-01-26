/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import group_theory.subgroup.basic -- import Lean's subgroups

/-

# Group homomorphisms

We show how to build the type `my_group_hom G H` of group homomorphisms
from `G` to `H`. We make notation `G →** H` for this, so `f : G →** H`
means "`f` is a group homomorphism from `G` to `H`".

-/

/-- `my_group_hom G H` is the type of group homomorphisms from `G` to `H`. -/
@[ext] structure my_group_hom (G H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' (a b : G) : to_fun (a * b) = to_fun a * to_fun b)

namespace my_group_hom

-- throughout this sheet, `G` and `H` will be groups.
variables {G H : Type} [group G] [group H]

-- We use notation `G →** H` for the type of group homs from `G` to `H`.
notation G ` →** ` H := my_group_hom G H

-- A group hom is a function, and so we set up a "coercion"
-- so that a group hom can be regarded as a function (even
-- though it's actually a pair consisting of a function and an axiom)
instance : has_coe_to_fun (G →** H) (λ _, G → H) :=
{ coe := my_group_hom.to_fun }

-- Notice that we can now write `f (a * b)` even though `f` isn't actually a
-- function, it's a pair consisting of a function `f.to_fun` and an axiom `f.map_mul'`.
-- The below lemma is how we want to use it as mathematicians though.
lemma map_mul (f : G →** H) (a b : G) : 
  f (a * b) = f a * f b :=
begin
  -- the point is that f.map_mul and f.map_mul' are *definitionally equal*
  -- but *syntactically different*, and the primed version looks uglier.
  -- The point of this lemma is that `f.map_mul` looks nicer.
  exact f.map_mul' a b
end

-- let `f` be a group hom
variable (f : G →** H)

-- To prove `map_one` you're going to need to know what the below lemma
-- is called. Uncomment it, look at the output, and remember it. It's
-- a useful part of the group theory API.

-- example (a b : G) : a * b = b ↔ a = 1 := mul_left_eq_self

-- Now see if you can do these.
@[simp] lemma map_one : f 1 = 1 :=
begin
  have h := f.map_mul 1 1,
  simpa using h,
end

lemma map_inv (a : G) : f a⁻¹ = (f a)⁻¹ :=
begin
  rw ← mul_eq_one_iff_eq_inv,
  rw ← f.map_mul,
  simp,
end

variable (G)

/-- `id G` is the identity group homomorphism from `G` to `G`. -/
def id : G →** G :=
{ to_fun := λ a, a,
  map_mul' := begin intros, refl, end }

variables {K : Type} [group K] {G}

/-- `φ.comp ψ` is the composite of `φ` and `ψ`. -/
def comp (φ : G →** H) (ψ : H →** K) : G →** K :=
{ to_fun := λ g, ψ (φ g),
  map_mul' := begin
    intros a b,
    rw [φ.map_mul, ψ.map_mul],
  end
}

-- The next three lemmas are pretty standard, but they are also in fact
-- the axioms that show that groups form a category.
lemma id_comp : (id G).comp f = f :=
begin
  ext g,
  refl,
end

lemma comp_id : f.comp (id H) = f :=
begin
  ext g,
  refl,
end

lemma comp_assoc {L : Type} [group L] (φ : G →** H) (ψ : H →** K) (ρ : K →** L) :
  (φ.comp ψ).comp ρ = φ.comp (ψ.comp ρ) :=
begin
  refl,
end

/-- The kernel of a group homomorphism, as a subgroup of the source group. -/
def ker (f : G →** H) : subgroup G :=
{ carrier := {g : G | f g = 1 },
  one_mem' := f.map_one,
  mul_mem' := begin
    intros a b ha hb,
    simp [f.map_mul, *] at *,
  end,
  inv_mem' := begin
    intros a ha,
    simp [f.map_inv, *] at *,
  end,
}

/-- The image of a group homomorphism, as a subgroup of the target group. -/
def im (f : G →** H) : subgroup H :=
{ carrier := {h : H | ∃ g : G, f g = h },
  one_mem' := begin 
    use 1,
    exact f.map_one,
  end,
  mul_mem' := begin
    rintro c d ⟨a, ha⟩ ⟨b, hb⟩,
    exact ⟨a * b, by rw [f.map_mul, ha, hb]⟩,
  end,
  inv_mem' := begin
    rintro c ⟨a, ha⟩,
    exact ⟨a⁻¹, by rw [f.map_inv, ha]⟩,
  end,
}

/-- The image of a subgroup under a group homomorphism, as a subgroup. -/
def map (f : G →** H) (K : subgroup G) : subgroup H :=
{ carrier := {h : H | ∃ g : G, g ∈ K ∧ f g = h },
  one_mem' := ⟨1, K.one_mem, f.map_one⟩,
  mul_mem' := begin
    rintro c d ⟨a, haK, rfl⟩ ⟨b, hbK, rfl⟩,
    refine ⟨a * b, K.mul_mem haK hbK, f.map_mul a b⟩,
  end,
  inv_mem' := begin
    intro x,
    intro hx,
    change ∃ a, _ at hx,
    cases hx with a ha,
    cases ha with haK hax,
    change ∃ b, _,
    use a⁻¹,
    split,
    { exact K.inv_mem haK },
    { subst hax, apply f.map_inv }
  end,
}

/-- The preimage of a subgroup under a group homomorphism, as a subgroup. -/
def comap (f : G →** H) (K : subgroup H) : subgroup G :=
{ carrier := {g : G | f g ∈ K },
  one_mem' := begin
    simp [K.one_mem],
  end,
  mul_mem' := begin
    intros a b ha hb,
    have h := K.mul_mem ha hb,
    rwa ← f.map_mul at h,
  end,
  inv_mem' := begin 
    intros a ha,
    replace ha := K.inv_mem ha,
    rwa ← f.map_inv at ha,
  end,
}

lemma map_id (L : subgroup G) : (id G).map L = L :=
begin
  ext g,
  split,
  { intro h,
    rcases h with ⟨x, hx1, rfl⟩,
    exact hx1 },
  { intro h,
    use g,
    exact ⟨h, rfl⟩ },
end

/-- Pushing a subgroup along one homomorphism and then another is equal to
  pushing it forward along the composite of the homomorphisms. -/
lemma map_comp (φ : G →** H) (ψ : H →** K) (L : subgroup G) :
  (φ.comp ψ).map L = ψ.map (φ.map L) :=
begin
  ext x,
  split,
  { rintro ⟨g, hgL, rfl⟩,
    use φ g,
    split,
    { exact ⟨g, hgL, rfl⟩ },
    { refl } },
  { rintro ⟨h, ⟨g, hgL, rfl⟩, rfl⟩,
    exact ⟨g, hgL, rfl⟩ },
end

lemma comap_id (L : subgroup G) : (id G).comap L = L :=
begin
  ext g,
  refl,
end

/-- Pulling a subgroup back along one homomorphism and then another, is equal
to pulling it back along the composite of the homomorphisms. -/
lemma comap_comp (φ : G →** H) (ψ : H →** K) (L : subgroup K) :
  (φ.comp ψ).comap L = φ.comap (ψ.comap L) :=
begin
  refl,
end

end my_group_hom
