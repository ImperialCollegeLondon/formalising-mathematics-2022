/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import section14polynomials.sheet04aux_ideal2

/-!

# Hilbert basis theorem

With those prerequisites out the way, let's prove the Hilbert Basis Theorem.

-/

variables {R : Type} [comm_ring R] (I : ideal (polynomial R))

open polynomial

theorem Hilbert_basis (hR : is_noetherian_ring R) : is_noetherian_ring (polynomial R) :=
begin
  -- A ring is Noetherian iff all ideals are finitely-generated. So let `I` be an
  -- ideal of `R[X]`. Now by `aux_ideal2.canonical_N I hR` there's a natural `N`
  -- such that `N ≤ m` implies `aux_ideal I n = aux_ideal2 I`. Now let `S` be

  -- finset.bUnion (finset.range (N+1)) 
  --  (λ n, (hR.gens (aux_ideal I n)).image (λ r, aux_ideal.lift I n r) ),

  -- That is, the union of the lifts of the generators of `aux_ideal I n`
  -- for `n ≤ N`. We claim that this `S` is a finite generating set of `I`. 
  -- First we prove that `ideal.span S ≤ I`; this is not so hard, because
  -- `S` is a subset of `I` by `aux_ideal.lift_mem_I`. What remains is
  -- the boss battle: to show that `I ≤ ideal.span S`.

  -- So let `f` be in `I`. We prove the result by strong induction on `f.nat_degree`.
  -- It suffices to prove that

  -- ∃ (g : polynomial R), g.nat_degree ≤ d ∧ 
  --    g ∈ ideal.span (S : set (polynomial R)) ∧ 
  --    g.coeff d = f.coeff d,

  -- because we can use the induction hypothesis. 

  -- To find this `g` we do a case split on whether d ≤ N or not. 
  -- If it is then you can use `aux_ideal.coeff_span_lift_gens` to get `g`,
  -- and if N+1+e=d you can use X^(e+1) times the polynomial coming
  -- from `aux_ideal.coeff_span_lift_gens`. 
  sorry
end