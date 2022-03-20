/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.polynomial

/-!

# Hilbert basis theorem

-/

namespace polynomial

variables (R : Type) [comm_ring R]

-- for mathlib
lemma nat_degree_X_pow_le (n : ℕ) : (X^n : polynomial R).nat_degree ≤ n :=
begin
  casesI subsingleton_or_nontrivial R,
  { rw nat_degree_of_subsingleton, exact zero_le n, },
  { rw nat_degree_X_pow },
end


noncomputable def Mnat (n : ℕ) : submodule R (polynomial R) :=
{ carrier := {f : polynomial R | f.nat_degree ≤ n},
  zero_mem' := begin exact zero_le n, end,
  add_mem' := begin
    intros f g hf hg, 
    dsimp at *, 
    apply (nat_degree_add_le f g).trans, 
    rw max_le_iff,
    exact ⟨hf, hg⟩,
  end,
  smul_mem' := begin
    intros c f hf,
    exact (nat_degree_smul_le c f).trans hf,
  end }

lemma mem_Mnat_iff (f : polynomial R) (n : ℕ) : f ∈ Mnat R n ↔ f.nat_degree ≤ n :=
begin
  refl
end

noncomputable def coeff' (n : ℕ) : polynomial R →ₗ[R] R :=
{ to_fun := λ f, f.coeff n,
  map_add' := λ f g, coeff_add f g n,
  map_smul' := λ r f, coeff_smul r f n }

lemma ker_coeff' (f : polynomial R) (n : ℕ) (hfn : f ∈ Mnat R n.succ) (hf : coeff' R n.succ f = 0) :
  f ∈ Mnat R n :=
begin
  rw mem_Mnat_iff at ⊢ hfn,
  rw nat_degree_le_iff_coeff_eq_zero at hfn ⊢,
  intros i hi,
  by_cases hin : n + 1 < i,
  { exact hfn _ hin, },
  { convert hf,
    rw nat.succ_eq_add_one,
    linarith },
end

end polynomial

variables {R : Type} [comm_ring R] (I : ideal (polynomial R))

open polynomial

-- for mathlib
namespace is_noetherian_ring

noncomputable def gens (hR : is_noetherian_ring R) (J : ideal R) : finset R :=
((is_noetherian_ring_iff_ideal_fg R).1 hR J).some

lemma span_gens (hR : is_noetherian_ring R) (J : ideal R) : ideal.span (hR.gens J : set R) = J :=
((is_noetherian_ring_iff_ideal_fg R).1 hR J).some_spec

lemma gens_subset (hR : is_noetherian_ring R) (J : ideal R) :
  (hR.gens J : set R) ⊆ J :=
begin
  convert ideal.subset_span,
  rw hR.span_gens,
end

end is_noetherian_ring

noncomputable def aux_ideal (n : ℕ) :=
(I.restrict_scalars R ⊓ Mnat R n).map (coeff' R n)

namespace aux_ideal

noncomputable def lift (n : ℕ) (r : R) [decidable (r ∈ aux_ideal I n)] : polynomial R :=
if hr : r ∈ aux_ideal I n then (submodule.mem_map.1 hr).some else 0

variables {n : ℕ} {r : R} [decidable (r ∈ aux_ideal I n)]

variable {I}

lemma lift_eq_zero_of_ne (hr : ¬ r ∈ aux_ideal I n) : lift I n r = 0 :=
dif_neg hr

lemma lift_mem :
  (lift I n r) ∈ submodule.restrict_scalars R I ⊓ Mnat R n :=
begin
  by_cases hr : r ∈ aux_ideal I n,
  { convert ((submodule.mem_map.1 hr).some_spec).1,
    exact dif_pos hr },
  { rw lift_eq_zero_of_ne hr,
    apply submodule.zero_mem, }
end

lemma lift_mem_I : lift I n r ∈ I :=
lift_mem.1

lemma lift_nat_degree_le :
  (lift I n r).nat_degree ≤ n :=
lift_mem.2

lemma lift_spec (hr : r ∈ aux_ideal I n) :
  coeff' R n (lift I n r) = r :=
begin
  convert ((submodule.mem_map.1 hr).some_spec).2,
  exact dif_pos hr,
end

variable (I)

lemma mono_aux (n : ℕ) :
  aux_ideal I n ≤ aux_ideal I (n + 1) :=
begin
  rintros - ⟨f, ⟨(hf1 : f ∈ I.restrict_scalars R), (hf2 : f.nat_degree ≤ n)⟩, rfl⟩,
  refine ⟨X * f, ⟨I.smul_mem X hf1, le_trans nat_degree_mul_le _⟩, coeff_X_mul f n⟩,
  have hX : (X : polynomial R).nat_degree ≤ 1 := nat_degree_X_le,
  linarith
end

lemma mono : monotone (aux_ideal I) :=
monotone_nat_of_le_succ (mono_aux I)

lemma coeff_span_lift_gens [∀ r, decidable (r ∈ aux_ideal I n)] [decidable_eq (polynomial R)] 
  (hR : is_noetherian_ring R) {c : R} (hcI : c ∈ aux_ideal I n) :
∃ (y : polynomial R), y ∈ submodule.span R ((λ (r : R), lift I n r) '' ↑(hR.gens (aux_ideal I n))) ∧
  (coeff' R n) y = c :=
begin
  rw ← hR.span_gens (aux_ideal I n) at hcI,
  change _ ∈ submodule.span R _ at hcI,
  have h : (hR.gens (aux_ideal I n) : set R) ⊆ (polynomial.coeff' R n)'' 
    (finset.image (λ (r : R), aux_ideal.lift I n r) (hR.gens (aux_ideal I n))),
  { intros x hx,
    refine ⟨aux_ideal.lift I n x, _, aux_ideal.lift_spec (hR.gens_subset _ hx)⟩,
    simp only [set.mem_image, finset.mem_coe, finset.coe_image],
    exact ⟨x, hx, rfl⟩ },
  replace hcI := submodule.span_mono h hcI,
  rw submodule.span_image at hcI,
  simpa using hcI,
end

lemma nat_deg_le_of_mem_span_lift_gens [∀ r, decidable (r ∈ aux_ideal I n)] 
  (hR : is_noetherian_ring R) {p : polynomial R}
  (hp : p ∈ submodule.span R ((λ (r : R), lift I n r) '' (hR.gens (aux_ideal I n)))) :
p.nat_degree ≤ n :=
begin
  rw ← mem_Mnat_iff,
  revert hp,
  apply submodule.span_le.2,
  intros x hx,
  simp only [set.mem_image, finset.mem_coe, finset.coe_image] at hx,
  rcases hx with ⟨y, hy, rfl⟩,
  apply aux_ideal.lift_nat_degree_le,
end

end aux_ideal

def aux_ideal2 (I : ideal (polynomial R)) : ideal R :=
{ carrier := ⋃ n, aux_ideal I n,
  zero_mem' := begin
    rw set.mem_Union,
    exact ⟨0, (aux_ideal I 0).zero_mem⟩,
  end,
  add_mem' := begin
    intros a b ha hb,
    rw set.mem_Union at ha hb ⊢,
    rcases ha with ⟨i, hi⟩,
    rcases hb with ⟨j, hj⟩,
    use max i j,
    apply (aux_ideal I _).add_mem,
    { exact aux_ideal.mono I (le_max_left i j) hi },
    { exact aux_ideal.mono I (le_max_right i j) hj }
  end,
  smul_mem' := begin
    intros c a ha,
    rw set.mem_Union at ha ⊢,
    rcases ha with ⟨i, hi⟩,
    use i,
    exact (aux_ideal I i).smul_mem c hi,
  end }

namespace aux_ideal2

lemma mem (I : ideal (polynomial R)) (j : R) (hj : j ∈ aux_ideal2 I) :
  ∃ m, j ∈ aux_ideal I m :=
set.mem_Union.1 hj

lemma mem_iff (I : ideal (polynomial R)) (j : R) :
 j ∈ aux_ideal2 I ↔ ∃ m, j ∈ aux_ideal I m :=
set.mem_Union 

lemma canonical_N (hR : is_noetherian_ring R) : 
  ∃ N, ∀ m, N ≤ m → aux_ideal2 I = aux_ideal I m :=
begin
  rw is_noetherian_ring_iff_ideal_fg at hR,
  cases hR (aux_ideal2 I) with S hS,
  choose g hg using aux_ideal2.mem I,
  have hSmem : ∀ s : R, s ∈ S → s ∈ aux_ideal2 I,
  { intros s hs,
    rw ← hS,
    apply ideal.subset_span,
    exact hs,
  },
  classical,
  use finset.sup S (λ r, if hr : r ∈ aux_ideal2 I then g r hr else 37),
  intros n hn,
  apply le_antisymm,
  { rw ← hS,
    rw ideal.span_le,
    rw finset.sup_le_iff at hn,
    intros s hs,
    specialize hn s hs,
    rw dif_pos (hSmem s hs) at hn,
    apply aux_ideal.mono I hn,
    apply hg },
  { intros r hr,
    rw aux_ideal2.mem_iff,
    exact ⟨n, hr⟩ }
end

end aux_ideal2

theorem Hilbert_basis (hR : is_noetherian_ring R) : is_noetherian_ring (polynomial R) :=
begin
  rw is_noetherian_ring_iff_ideal_fg,
  intro I,
  cases aux_ideal2.canonical_N I hR with N hN,
  classical,
  let S := finset.bUnion (finset.range N.succ) 
    (λ n, (hR.gens (aux_ideal I n)).image (λ r, aux_ideal.lift I n r) ),
  use S,
  have hSI : ideal.span (S : set (polynomial R)) ≤ I,
  { rw ideal.span_le,
    intros x hx,
    rcases finset.mem_bUnion.1 hx with ⟨m, hm, hx⟩,
    rw finset.mem_image at hx,
    rcases hx with ⟨r, hr, rfl⟩,
    apply aux_ideal.lift_mem_I },
  apply le_antisymm hSI,
  { -- boss level
    intro f,
    --by_cases hdeg : f.nat_degree ≤ N,
    induction h : f.nat_degree using nat.strong_induction_on with d hd generalizing f,
    dsimp at hd,
    intro hfI,
    suffices : ∃ (g : polynomial R), g.nat_degree ≤ d ∧ 
      g ∈ ideal.span (S : set (polynomial R)) ∧ 
      g.coeff d = f.coeff d,
    { rcases this with ⟨g, hgdeg, hgS, hcoeff⟩,
      cases d,
      { convert hgS, 
        ext,
        cases n, rw hcoeff,
        rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt],
        { exact lt_of_le_of_lt hgdeg n.zero_lt_succ, },
        { exact h.symm ▸ (n.zero_lt_succ), },
      },
      { rw (show f = (f - g) + g, by ring),
        refine ideal.add_mem _ _ hgS,
        have hfg : (f - g).nat_degree < d.succ, 
        { rw lt_iff_le_and_ne,
          split, 
          { rw sub_eq_add_neg,
            convert le_trans (nat_degree_add_le f (-g)) _,
            apply max_le h.le,
            rwa nat_degree_neg },
          { intro h1, 
            have h2 : (f - g).coeff d.succ = 0,
            { rw [coeff_sub, hcoeff, sub_self] },
            rw ← h1 at h2,
            rw [coeff_nat_degree, leading_coeff_eq_zero] at h2,
            rw [h2, nat_degree_zero] at h1,
            cases h1 } },
        apply hd _ hfg rfl,
        apply I.sub_mem hfI,
        exact hSI hgS },
    },
    clear hd hSI,
    set c := coeff' R d f with hc,
    have hcI : c ∈ aux_ideal I d := ⟨f, ⟨hfI, h.le⟩, hc.symm⟩, 
    cases lt_or_le d (N+1) with hdN hdN,
    { obtain ⟨g, hg, hgc⟩ := aux_ideal.coeff_span_lift_gens I hR hcI,
      refine ⟨g, (aux_ideal.nat_deg_le_of_mem_span_lift_gens I hR hg), _, hgc.trans hc⟩,
      refine submodule.span_subset_span R (polynomial R) _ _,
      refine submodule.span_mono _ hg,
      rintro x hx,
      simp only [set.mem_image, finset.mem_coe, finset.coe_image] at hx,
      rcases hx with ⟨y, hy, rfl⟩,
      simp only [exists_prop, set.mem_Union, finset.coe_bUnion, set.mem_image, finset.mem_range, finset.mem_coe, finset.coe_image],
      refine ⟨d, hdN, y, hy, rfl⟩ },
    { rw ← hN d (lt_of_lt_of_le N.lt_succ_self hdN).le at hcI,
      rw hN N N.le_refl at hcI,
      obtain ⟨p, hp, hpc⟩ := aux_ideal.coeff_span_lift_gens I hR hcI,
      rw le_iff_exists_add at hdN,
      rcases hdN with ⟨e, rfl⟩,
      rw (show N + 1 + e = N + (e + 1), by ring) at *,
      have hpdeg : p.nat_degree ≤ N := aux_ideal.nat_deg_le_of_mem_span_lift_gens I hR hp,
      refine ⟨p * X^(e+1), _, _, _⟩,
      { refine nat_degree_mul_le.trans _,
        refine add_le_add hpdeg _,
        apply nat_degree_X_pow_le },
      { refine ideal.mul_mem_right _ _ _,
        refine submodule.span_subset_span R (polynomial R) _ _,
        refine submodule.span_mono _ hp,
        rintro x hx,
        simp only [set.mem_image, finset.mem_coe, finset.coe_image] at hx,
        rcases hx with ⟨y, hy, rfl⟩,
        simp only [exists_prop, set.mem_Union, finset.coe_bUnion, set.mem_image, finset.mem_range, finset.mem_coe, finset.coe_image],
        refine ⟨N, N.lt_succ_self, y, hy, rfl⟩, },
      { rw coeff_mul_X_pow, 
        exact hpc.trans hc },
    } },
end