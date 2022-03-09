import tactic -- for the tactics
import ring_theory.ideal.operations -- for the ideals
-- (including product of ideals)

-- universe variable
universe u

variables (R : Type u) [comm_ring R]

-- let V be a vector space over R (i.e. a module over R)
variables (V : Type u) [add_comm_group V] [module R V]
  
-- the R-linear isomorphism `V ≃ₗ[R] V`
#check linear_equiv.refl R V
-- linear_equiv.refl R V : V ≃ₗ[R] V

-- Note that this isn't the true-false statement "V is isomorphic to V",
-- it's the actual identity isomorphism V ≃ V.

namespace submodule

-- This function is in Mathlib as of Feb 2022 but
-- I don't want to change the version of mathlib
-- in the project, which I made in Jan 2022

/-- A dependent version of `submodule.span_induction`. -/
lemma span_induction'' {R : Type*} [semiring R] {M : Type*} [add_comm_monoid M] [module R M] 
  {s : set M} {p : Π x, x ∈ span R s → Prop}
  (Hs : ∀ x (h : x ∈ s), p x (subset_span h))
  (H0 : p 0 (submodule.zero_mem _))
  (H1 : ∀ x hx y hy, p x hx → p y hy → p (x + y) (submodule.add_mem _ ‹_› ‹_›))
  (H2 : ∀ (a : R) x hx, p x hx → p (a • x) (submodule.smul_mem _ _ ‹_›)) {x} (hx : x ∈ span R s) :
  p x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ span R s) (hc : p x hx), hc),
  refine span_induction hx (λ m hm, ⟨subset_span hm, Hs m hm⟩) ⟨zero_mem _, H0⟩
    (λ x y hx hy, exists.elim hx $ λ hx' hx, exists.elim hy $ λ hy' hy,
    ⟨add_mem _ hx' hy', H1 _ _ _ _ hx hy⟩) (λ r x hx, exists.elim hx $ λ hx' hx,
    ⟨smul_mem _ _ hx', H2 r _ _ hx⟩)
end

end submodule

namespace ideal

def s (R : Type u) [comm_ring R] : setoid (ideal R) :=
{ r := λ I J, nonempty (I ≃ₗ[R] J),
  iseqv := begin
    refine ⟨_, _, _⟩,
    { intro K,
      exact nonempty.intro (linear_equiv.refl R K) },
    { rintros I J ⟨hIJ⟩,
      exact nonempty.intro hIJ.symm },
    { rintros I J K ⟨hIJ⟩ ⟨hJK⟩,
      exact nonempty.intro (hIJ.trans hJK) },
  end }

-- The below stuff (the next 150 lines0 seems to be missing from mathlib; it's basic facts about
-- how isomorphism of ideals plays with multiplication of ideals.
-- It's quite advanced Lean I guess :-/ (I found it a pain to write)

variable {R}

/-- The R-linear map `J*I → K*I` induced by a linear map `e : J → K` of ideals. -/
def linear_map.rmul (I : ideal R) {J K : ideal R} (e : J →ₗ[R] K) :
  (J * I : ideal R) →ₗ[R] (K * I : ideal R) :=
{ to_fun := λ x, ⟨e ⟨x.1, mul_le_right x.2⟩, begin
    cases x with x hx,
    have h2 : x ∈ J := mul_le_right hx,
    rw (show mul_le_right hx = h2, from rfl),
    dsimp,
    rw submodule.mul_eq_span_mul_set at hx,
    revert h2,
    refine submodule.span_induction'' _ _ _ _ hx,
    { rintro x_1 ⟨r, s, hr, hs, rfl⟩ h2,
      simp only [mul_comm r s, mul_comm K I],
      convert mul_mem_mul hs (e ⟨r, hr⟩).2,
      have := e.map_smul s ⟨r, hr⟩,
      apply_fun subtype.val at this,
      exact this },
    { intro _,
      convert (K * I).zero_mem, -- simp, simp doesn't give an error
      have := e.map_zero,
      apply_fun subtype.val at this,
      exact this },
    { rintros a ha b hb,
      rw ← submodule.mul_eq_span_mul_set at ha hb,
      intros haKI hbKI,
      have haJ := (mul_le_right ha),
      have hbJ := (mul_le_right hb),
      specialize haKI haJ,
      specialize hbKI hbJ,
      rintro _,
      have := e.map_add ⟨a, haJ⟩ ⟨b, hbJ⟩,
      apply_fun subtype.val at this,
      convert (K * I).add_mem haKI hbKI },
    { rintros r b hb,
      rw ← submodule.mul_eq_span_mul_set at hb,
      intros hbKI,
      have hbJ := (mul_le_right hb),
      specialize hbKI hbJ,
      rintro _,
      have := e.map_smul r ⟨b, hbJ⟩,
      apply_fun subtype.val at this,
      convert (K * I).smul_mem r hbKI },
  end⟩,
  map_add' := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩,
    apply subtype.ext,
    have := e.map_add ⟨a, mul_le_right ha⟩ ⟨b, mul_le_right hb⟩,
    apply_fun subtype.val at this,
    exact this,
  end,
  map_smul' := begin
    rintros r ⟨a, ha⟩,
    apply subtype.ext,
    have := e.map_smul r ⟨a, mul_le_right ha⟩,
    apply_fun subtype.val at this,
    exact this,
  end }

def linear_equiv.rmul (I : ideal R) {J K : ideal R} (e : J ≃ₗ[R] K) : 
  (J * I : ideal R) ≃ₗ[R] (K * I : ideal R) :=
{ inv_fun := linear_map.rmul I e.symm.to_linear_map,
  left_inv := begin
    intro x,
    simp [linear_map.rmul],
  end,
  right_inv := begin
    rintro ⟨x, hx⟩,
    simp [linear_map.rmul],
  end,
  ..linear_map.rmul I e.to_linear_map }

def linear_map.lmul (I : ideal R) {J K : ideal R} (e : J →ₗ[R] K) : 
  (I * J : ideal R) →ₗ[R] (I * K : ideal R) :=
{ to_fun := λ x, ⟨e ⟨x.1, mul_le_left x.2⟩, begin
    cases x with x hx,
    have h2 : x ∈ J := mul_le_left hx,
    rw (show mul_le_left hx = h2, from rfl),
    dsimp,
    rw submodule.mul_eq_span_mul_set at hx,
    revert h2,
    refine submodule.span_induction'' _ _ _ _ hx,
    { rintro x_1 ⟨r, s, hr, hs, rfl⟩ h2,
      convert mul_mem_mul hr (e ⟨s, hs⟩).2,
      have := e.map_smul r ⟨s, hs⟩,
      apply_fun subtype.val at this,
      exact this },
    { intro _,
      convert (I * K).zero_mem, -- simp, simp doesn't give an error
      have := e.map_zero,
      apply_fun subtype.val at this,
      exact this },
    { rintros a ha b hb,
      rw ← submodule.mul_eq_span_mul_set at ha hb,
      intros haKI hbKI,
      have haJ := (mul_le_left ha),
      have hbJ := (mul_le_left hb),
      specialize haKI haJ,
      specialize hbKI hbJ,
      rintro _,
      have := e.map_add ⟨a, haJ⟩ ⟨b, hbJ⟩,
      apply_fun subtype.val at this,
      convert (I * K).add_mem haKI hbKI },
    { rintros r b hb,
      rw ← submodule.mul_eq_span_mul_set at hb,
      intros hbKI,
      have hbJ := (mul_le_left hb),
      specialize hbKI hbJ,
      rintro _,
      have := e.map_smul r ⟨b, hbJ⟩,
      apply_fun subtype.val at this,
      convert (I * K).smul_mem r hbKI },
  end⟩,
  map_add' := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩,
    apply subtype.ext,
    have := e.map_add ⟨a, mul_le_left ha⟩ ⟨b, mul_le_left hb⟩,
    apply_fun subtype.val at this,
    exact this,
  end,
  map_smul' := begin
    rintros r ⟨a, ha⟩,
    apply subtype.ext,
    have := e.map_smul r ⟨a, mul_le_left ha⟩,
    apply_fun subtype.val at this,
    exact this,
  end }

def linear_equiv.lmul (I : ideal R) {J K : ideal R} (e : J ≃ₗ[R] K) : 
  (I * J : ideal R) ≃ₗ[R] (I * K : ideal R) :=
{ inv_fun := linear_map.lmul I e.symm.to_linear_map,
  left_inv := begin
    intro x,
    simp [linear_map.lmul],
  end,
  right_inv := begin
    rintro ⟨x, hx⟩,
    simp [linear_map.lmul],
  end,
  ..linear_map.lmul I e.to_linear_map }

variable (R)


/-- Being isomorphic is a congruence relation on ideals (i.e., it plays well with `*`)-/
def con : con (ideal R) :=
{ mul' := begin
    rintros I J K L ⟨eIJ⟩ ⟨eKL⟩,
    refine ⟨_⟩,
    refine (ideal.linear_equiv.rmul K eIJ).trans (linear_equiv.lmul J eKL),
  end,
  ..ideal.s R }

-- quotienting out by the congruence relation
abbreviation Picard_monoid := (con R).quotient

-- and because we used `con.quotient` the quotient
-- gets a monoid instance automatically
instance : monoid (Picard_monoid R) := infer_instance

abbreviation Picard_group := units (Picard_monoid R)

end ideal

-- the Picard group of a commutative ring is a group
instance : group (ideal.Picard_group R) := by apply_instance 

