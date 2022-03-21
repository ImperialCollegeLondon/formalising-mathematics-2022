/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import section14polynomials.sheet03aux_ideal

/-!

This sheet contains a couple of trickier proofs about `aux_ideal`. 

Here is an explanation of the first -- igt's called `coeff_span_lift_gens`. 

Say R is Noetherian, and `c ∈ aux_ideal I n`. Recall that `hR.gens (aux_ideal I n)`
is a (finite) set which spans `aux_ideal I n` as an `R`-ideal. So in particular
we know that `c` is in the span of these generators.

The claim is that if we let `T : finset R[X]` be random `lift`s of these generators to `R[X]`,
then there's a polynomial `y` in the `R`-span of these lifts such that the coefficient of `X^n`
in `y` is `c` again.

One way of doing this would be to write `c` as a finite `R`-linear combination of the generators,
and then use the corresponding finite `R`-linear combination of the lifts. But that is a pain
to code. 

The proof I came up with of this uses `submodule.span_image`, which says that the span
of the image equals the image of the span. In particular, the image of the lifts is just
the generators `hR.gens (aux_ideal I n)` again, so the image of the span is `aux_ideal I n`.
The theorem says that this means that the image of the `R`-span of the lifts in `R[X]` under
the `coeff` map is `aux_ideal I n` and so our element `y` comes for free.

A key intermediate step in my proof is

have h : (hR.gens (aux_ideal I n) : set R) ⊆ (polynomial.lcoeff R n)'' 
    (finset.image (λ (r : R), aux_ideal.lift I n r) (hR.gens (aux_ideal I n))),

saying that the generators are a subset of the image of the lift of the generators.
I don't need to prove equality. After that it's just `submodule.span_image` and unravelling.
More precisely, `hcI` tells us that `c` is in the span of the generators, 
and `ideal.span_mono` reduces us to the case that `c` is in the span
of the image under an `R`-module map of some set (namely the image of `lift`),
By `submodule.span_image` we're now done.
-/

variables {R : Type} [comm_ring R] (I : ideal (polynomial R))
variables {n : ℕ} {r : R} [decidable (r ∈ aux_ideal I n)]

open polynomial

namespace aux_ideal

lemma coeff_span_lift_gens [∀ r, decidable (r ∈ aux_ideal I n)] [decidable_eq (polynomial R)] 
  (hR : is_noetherian_ring R) {c : R} (hcI : c ∈ aux_ideal I n) :
∃ (y : polynomial R), y ∈ submodule.span R ((λ (r : R), lift I n r) '' ↑(hR.gens (aux_ideal I n))) ∧
  (lcoeff R n) y = c :=
begin
  sorry
end

/-

The conclusion of the previous lemma says that there's some polynomial
in `submodule.span R ((λ (r : R), lift I n r) '' ↑(hR.gens (aux_ideal I n)))`. 
The below lemma shows that such a polynomial has degree at most `n`, and
the reason is simply that all the generators have degree at most `n`.
To solve this one you'll need to know `submodule.span_le` from mathlib
and `lift_nat_degree_le` from a previous sheet.
-/

lemma nat_deg_le_of_mem_span_lift_gens [∀ r, decidable (r ∈ aux_ideal I n)] 
  (hR : is_noetherian_ring R) {p : polynomial R}
  (hp : p ∈ submodule.span R ((λ (r : R), lift I n r) '' (hR.gens (aux_ideal I n)))) :
p.nat_degree ≤ n :=
begin
  sorry,
end

end aux_ideal
