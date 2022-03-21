/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import solutions.section14polynomials.sheet04more_aux_ideal

/-

Recall that we know `aux_ideal I n` is an increasing function of `n`.
In this file we define `aux_ideal2 I` to be the union over all `n`
of `aux_ideal I n`. Note that it is an ideal of `R`, so if `R` is
Noetherian then it's going to be finitely-generated. This is a key
ingredient im the proof.

-/

variables {R : Type} [comm_ring R] (I : ideal (polynomial R))

open polynomial

/-

Recall the key API for `⋃` is `set.mem_Union`
-/

/-- An auxiliary ideal used in the proof of Hilbert's Basis Theorem.
It's equal to the elements of `R` which are either 0, or the
leading coefficient of an element of `I`. Showing that this is an
ideal is made much easier by the fact that it can also be thought
of as a union of the increasing sequence of ideals `aux_ideal I n`. -/
def aux_ideal2 (I : ideal (polynomial R)) : ideal R :=
{ carrier := ⋃ n, aux_ideal I n,
  zero_mem' := begin
    rw set.mem_Union,
    use 37,
    exact ideal.zero_mem (aux_ideal I 37),
  end,
  add_mem' := begin
    intros f g hf hg,
    rw set.mem_Union at hf hg ⊢,
    rcases hf with ⟨a, ha⟩,
    rcases hg with ⟨b, hb⟩,
    use max a b,
    apply (aux_ideal I (max a b)).add_mem,
    { exact aux_ideal.mono _ (le_max_left a b) ha },
    { exact aux_ideal.mono _ (le_max_right a b) hb },
  end,
  smul_mem' := begin
    intros r f hf,
    rw set.mem_Union at hf ⊢,
    cases hf with i hi,
    use i,
    refine submodule.smul_mem (aux_ideal I i) r hi, 
  end }

namespace aux_ideal2

-- we make some helpful API.

lemma mem (I : ideal (polynomial R)) (j : R) (hj : j ∈ aux_ideal2 I) :
  ∃ m, j ∈ aux_ideal I m :=
set.mem_Union.1 hj

lemma mem_iff (I : ideal (polynomial R)) (j : R) :
 j ∈ aux_ideal2 I ↔ ∃ m, j ∈ aux_ideal I m :=
set.mem_Union

/-

Assume `R` is Noetherian. Because `aux_ideal2 I` is finitely-generated,
the increasing chain of ideals `aux_ideal I 0 ≤ aux_ideal I 1 ≤ aux_ideal I 2 ≤ ...`
must stabilise. 

Helpful API: `finset.sup`. Don't forget to use the `classical` tactic
if you run into decidability issues.

-/
lemma canonical_N (hR : is_noetherian_ring R) : 
  ∃ N, ∀ m, N ≤ m → aux_ideal2 I = aux_ideal I m :=
begin
  -- Q -- can this be done with `is_noetherian_iff_well_founded`?
  obtain ⟨S, hS⟩ := (is_noetherian_ring_iff_ideal_fg R).1 hR (aux_ideal2 I),
  have hSmem : ∀ r : R, r ∈ S → r ∈ aux_ideal2 I,
  { rw ← hS, intros r hr, exact ideal.subset_span hr },
  choose g hg using mem I,
  classical,
  use finset.sup S (λ r, if hr : r ∈ aux_ideal2 I then g r hr else 37),
  intros m hm,
  apply le_antisymm,
  { rw ← hS,
    rw ideal.span_le,
    intros r hrS,
    rw finset.sup_le_iff at hm,
    specialize hm r hrS,
    have hraux := hSmem _ hrS,
    rw dif_pos hraux at hm,
    apply aux_ideal.mono I hm,
    apply hg },
  { intros r hr,
    rw mem_iff,
    use m,
    assumption },
end

end aux_ideal2