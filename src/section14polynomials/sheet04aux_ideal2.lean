/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import section14polynomials.sheet03aux_ideal

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
    sorry,
  end,
  add_mem' := begin
    sorry,
  end,
  smul_mem' := begin
    sorry,
  end }

namespace aux_ideal2

-- we make some helpful API.

lemma mem (I : ideal (polynomial R)) (j : R) (hj : j ∈ aux_ideal2 I) :
  ∃ m, j ∈ aux_ideal I m :=
begin
  sorry
end

lemma mem_iff (I : ideal (polynomial R)) (j : R) :
 j ∈ aux_ideal2 I ↔ ∃ m, j ∈ aux_ideal I m :=
begin
  sorry
end

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
  sorry
end

end aux_ideal2