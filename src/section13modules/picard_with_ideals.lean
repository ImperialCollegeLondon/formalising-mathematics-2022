--import algebra.category.Module.basic
import ring_theory.ideal.basic
import linear_algebra.tensor_product

/-!

# Picard group of a commutative ring

-/
universe u

variables (R : Type u) [comm_ring R]

-- ideal version

namespace ideal

def s : setoid (ideal R) :=
{ r := λ I J, nonempty (I ≃ₗ[R] J),
  iseqv :=
  ⟨λ I, nonempty.intro $ linear_equiv.refl _ _, 
   λ I J hIJ, nonempty.intro $ hIJ.some.symm, 
   λ I J K hIJ hJK, nonempty.intro $ hIJ.some.trans hJK.some⟩ }

/-

The Picard monoid is the quotient by `s` as a bare type.

But let's make the quotient in a different way using `con`.

-/
def mul (I J : ideal R) : ideal R := ideal.span {r : R | ∃ (i ∈ I) (j ∈ J), r = i * j}

instance : has_mul (ideal R) :=
{ mul := mul R }

instance : has_one (ideal R) :=
{ one := ⊤ }

instance : monoid (ideal R) :=
{ mul := (*),
  one := 1,
  mul_assoc := λ I J K, begin
    apply le_antisymm,
    { apply span_le.2 _,
      rintro - ⟨i, hiIJ, k, hk, rfl⟩,
      apply submodule.span_induction hiIJ,
      { rintro - ⟨i, hi, j, hj, rfl⟩,
        apply subset_span,
        refine ⟨i, hi, j * k, subset_span ⟨j, hj, k, hk, rfl⟩, mul_assoc i j k⟩ },
      { simp },
      { intros a b ha hb, 
        simp [add_mul, ideal.add_mem (I * (J * K)) ha hb] },
      { intros a x h, change _ ∈ I * (J * K), 
        convert submodule.smul_mem (I * (J * K)) a h using 1, 
        simp [mul_assoc] } },
    { apply span_le.2 _,
      rintro - ⟨i, hi, jk, hjk, rfl⟩,
      apply submodule.span_induction hjk,
      { rintro - ⟨j, hj, k, hk, rfl⟩,
        apply subset_span,
        refine ⟨i * j, subset_span ⟨i, hi, j, hj, rfl⟩, 
          k, hk, (mul_assoc i j k).symm⟩, },
      { simp },
      { intros a b ha hb, 
        simp [mul_add, ideal.add_mem (I * J * K) ha hb], },
      { intros a x h, change _ ∈ I * J * K, 
        convert submodule.smul_mem (I * J * K) a h using 1, 
        simp [← mul_assoc, mul_left_comm], } },
  end,
  one_mul := begin 
    intro I,
    apply le_antisymm,
    { apply span_le.2 _,
      rintro - ⟨r, -, i, hi, rfl⟩,
      exact submodule.smul_mem I r hi },
    { intros i hi,
      apply subset_span,
      refine ⟨1, submodule.mem_top, i, hi, (one_mul i).symm⟩ },
  end,
  mul_one := λ I, begin 
    apply le_antisymm,
    { apply span_le.2 _,
      rintro - ⟨i, hi, r, -, rfl⟩,
      exact I.mul_mem_right r hi },
    { intros i hi,
      apply subset_span,
      refine ⟨i, hi, 1, submodule.mem_top, (mul_one i).symm⟩, },
    end, }

lemma mul_le_left {I J : ideal R} : I * J ≤ I :=
begin
  apply span_le.2,
  rintro a ⟨i, hi, j, hj, rfl⟩,
  apply ideal.mul_mem_right _ _ hi,
end

lemma mul_le_right {I J : ideal R} : I * J ≤ J :=
begin
  apply span_le.2,
  rintro a ⟨i, hi, j, hj, rfl⟩,
  apply ideal.mul_mem_left _ _ hj,
end

variable {R}

def linear_map.rmul (I : ideal R) {J K : ideal R} (e : J →ₗ[R] K) : 
  (J * I : ideal R) →ₗ[R] (K * I : ideal R) :=
{ to_fun := λ x, ⟨e.to_fun ⟨x.1, mul_le_left R x.2⟩, begin
    refine submodule.span_induction' _ _ _ _ x; clear x,
    { rintro - ⟨j, hj, i, hi, rfl⟩, 
      apply submodule.subset_span, 
      refine ⟨e ⟨j, hj⟩, (e ⟨j, hj⟩).2, i, hi, _⟩,
      simp_rw mul_comm j i,
      rw mul_comm (e ⟨j, hj⟩ : R) i,
      have h := e.map_smul i ⟨j, hj⟩,
      apply_fun subtype.val at h,
      exact h },
    { convert ideal.zero_mem _,
      simp,
      exact e.map_zero },
    { rintros ⟨x, hx⟩ ⟨y, hy⟩ hex hey,
      convert (K * I).add_mem hex hey,
      simp only [submodule.coe_add, submodule.coe_mk, linear_map.to_fun_eq_coe, subtype.val_eq_coe],
      have := e.map_add ⟨x, mul_le_left R hx⟩ ⟨y, mul_le_left R hy⟩,
      apply_fun subtype.val at this,
      exact this },
    { rintros r ⟨x, hx⟩ hex,
      convert (K * I).smul_mem r hex,
      simp,
      have := e.map_smul r ⟨x, mul_le_left R hx⟩,
      apply_fun subtype.val at this,
      exact this }
  end⟩,
  map_add' := begin
    rintros ⟨x, hx⟩ ⟨y, hy⟩, 
    apply subtype.coe_injective,
    have := e.map_add ⟨x, mul_le_left R hx⟩ ⟨y, mul_le_left R hy⟩,
    apply_fun subtype.val at this,
    exact this,
  end,
  map_smul' := begin
    rintros r ⟨x, hx⟩,
    apply subtype.coe_injective,
    have := e.map_smul r ⟨x, mul_le_left R hx⟩,
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
{ to_fun := λ x, ⟨e.to_fun ⟨x.1, mul_le_right R x.2⟩, begin
    refine submodule.span_induction' _ _ _ _ x; clear x,
    { rintro - ⟨i, hi, j, hj, rfl⟩, 
      apply submodule.subset_span, 
      refine ⟨i, hi, e ⟨j, hj⟩, (e ⟨j, hj⟩).2, _⟩,
      have h := e.map_smul i ⟨j, hj⟩,
      apply_fun subtype.val at h,
      exact h },
    { convert ideal.zero_mem _,
      simp,
      exact e.map_zero },
    { rintros ⟨x, hx⟩ ⟨y, hy⟩ hex hey,
      convert (I * K).add_mem hex hey,
      simp only [submodule.coe_add, submodule.coe_mk, linear_map.to_fun_eq_coe, subtype.val_eq_coe],
      have := e.map_add ⟨x, mul_le_right R hx⟩ ⟨y, mul_le_right R hy⟩,
      apply_fun subtype.val at this,
      exact this },
    { rintros r ⟨x, hx⟩ hex,
      convert (I * K).smul_mem r hex,
      simp,
      have := e.map_smul r ⟨x, mul_le_right R hx⟩,
      apply_fun subtype.val at this,
      exact this }
  end⟩,
  map_add' := begin
    rintros ⟨x, hx⟩ ⟨y, hy⟩, 
    apply subtype.coe_injective,
    have := e.map_add ⟨x, mul_le_right R hx⟩ ⟨y, mul_le_right R hy⟩,
    apply_fun subtype.val at this,
    exact this,
  end,
  map_smul' := begin
    rintros r ⟨x, hx⟩,
    apply subtype.coe_injective,
    have := e.map_smul r ⟨x, mul_le_right R hx⟩,
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

-- It's true
def con : con (ideal R) :=
{ mul' := begin
    rintros I J K L ⟨eIJ⟩ ⟨eKL⟩,
    refine ⟨_⟩,
    refine (ideal.linear_equiv.rmul K eIJ).trans (ideal.linear_equiv.lmul J eKL),
  end,
  ..ideal.s R }

attribute [instance] ideal.s

abbreviation Picard_monoid := (ideal.con R).quotient

example : monoid ((ideal.con R).quotient) := con.monoid (ideal.con R)

instance : monoid (ideal.Picard_monoid R) := con.monoid (ideal.con R)

-- The ideal-theoretic definition of the Picard group
abbreviation Picard_group := units (ideal.Picard_monoid R)

instance : group (ideal.Picard_group R) := infer_instance -- works

#check ideal.Picard_group R -- Type u

-- But is it the same as the module one??

-- notation
open_locale tensor_product

variable {R}

def are_tensor_inverses (I J : ideal R) : Prop :=
nonempty (I ⊗[R] J ≃ₗ[R] R)

lemma are_tensor_inverses.symm {I J : ideal R} (e : are_tensor_inverses I J) :
  are_tensor_inverses J I :=
nonempty.map (λ i, linear_equiv.trans (tensor_product.comm R _ _) i) e

def is_tensor_invertible (I : ideal R) : Prop := 
∃ J : ideal R, nonempty (I ⊗[R] J ≃ₗ[R] R)

namespace is_tensor_invertible

variable (I : ideal R)

lemma tensor_iso_prod (h : is_tensor_invertible I) (K : ideal R) :
  nonempty (K ⊗[R] I ≃ (K * I : ideal R)) :=
begin
  -- Antoine said this might be some standard fact about
  -- invertible ideals
  sorry
end 

variable (R)

abbreviation bundled_tensor_invertible_ideals := {I : ideal R // is_tensor_invertible I}

instance s : setoid (bundled_tensor_invertible_ideals R) :=
{ r := λ I J, nonempty (I.1 ≃ₗ[R] J.1),
  iseqv := 
  ⟨λ I, nonempty.intro $ linear_equiv.refl _ _,  
   λ I J, nonempty.map linear_equiv.symm,
   λ I J K, nonempty.map2 linear_equiv.trans⟩ }

end is_tensor_invertible

end ideal
