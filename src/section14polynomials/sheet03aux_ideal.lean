/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import section14polynomials.sheet02noetherian

/-!

# An auxiliary construction

I haven't talked about which proof of the Hilbert Basis Theorem we'll
be formalising, so let me say a bit about this here. The theorem
states that if `R` is a Noetherian (commutative) ring then so is
the polynomial ring `R[X]`. So, given an ideal `I` of `R[X]` we need
to come up with a finite set of generators, and the only tool we have
is that any ideal of `R` has a finite set of generators. So, however
this proof goes, we are going to probably be wanting to construct
ideals of `R` given an ideal of `R[X]`. 

The `aux_ideal` construction is of this nature. An ideal of `R[X]`
is by definition an `R[X]`-submodule of `R[X]` so it's also
an `R`-submodule of `R[X]` (this is a bit like saying that a complex
vector space is obviously also a real vector space). The `lcoeff`
maps, taking a polynomial to its coefficient of `X^n`,  are `R`-linear
maps from `R[X]` to `R`, so we can push `R`-submodules of `R[X]` along
these maps (i.e. look at their images) to get `R`-submodules of `R`,
which is the same thing as ideals of `R`. The submodules we will push
forward are the following: given an ideal `I` of `R[X]`, and a natural
number `n`, we will consider `I` as an `R`-submodule of `R[X]`, we will
intersect it with `M R n` (the `R`-submodule of polynomials of degree
at most `n`), and we will then look at its image under `lcoeff R n`.
By definition then, the elements of `aux_ideal I n` will be the
coeficients of `X^n` of the polynomials in `I` which have degree
at most `n`, and this abstract way of describing this set shows that
it is an ideal of `R`.

Again, more briefly: if `I` is an ideal of `R[X]` and `n` is a natural,
then `aux_ideal I n` is the ideal of `R` consisting of the coefficients
of `X^n` of the elements of `I` with `nat_degree` at most `n`. 

The first result we are aiming for in this file is that
`aux_ideal I n` is monotone as a function of `n`, that is, if `n ≤ m`
then `aux_ideal I n ≤ aux_ideal I m`.

-/

variables {R : Type} [comm_ring R] (I : ideal (polynomial R))

open polynomial

/-

`I.restrict_scalars R` means the ideal `I`, regarded as an `R`-submodule
of `R[X]`. The `⊓` is just intersection of submodules. The `map`
is `submodule.map` which is the function which eats a linear map
(in this case `lcoeff R n`) and outputs a function sending submodules
of the domain of the map to submodules of the codomain; the function
itself is just "image of the submodule under the linear map".

-/
noncomputable def aux_ideal (n : ℕ) :=
(I.restrict_scalars R ⊓ M R n).map (lcoeff R n)

namespace aux_ideal

/-

Make sure you know a maths proof before embarking on this.

Useful API: 

`I.smul_mem r : x ∈ I → r * x ∈ I`
`polynomial.nat_degree_mul_le : (p * q).nat_degree ≤ p.nat_degree + q.nat_degree`
`p.coeff_X_mul : (n : ℕ), (X * p).coeff (n + 1) = p.coeff n`

and note that `lcoeff R n f` is definitionally `f.coeff n`.

-/

lemma mono_aux (n : ℕ) :
  aux_ideal I n ≤ aux_ideal I (n + 1) :=
begin
  sorry,
end

-- this is now a one-liner
lemma mono : monotone (aux_ideal I) :=
begin
  sorry
end

/- Given an ideal `I` and a natural number `n`, we have been
considering the map from `I ∩ {degree ≤ n}` to `R` defined by
"take coefficient of `X^n`". The `lift` function below is
a one-sided inverse to this map. Given an element of `R`,
if it's in the image then we send it to a random preimage
in `I ∩ (degree ≤ n)` and if it's not then we just send it to 0.
Note the use of `exists.some`; the statement "I am in the image"
is definitionally equal to "there exists something in the domain
which maps to me", and `exists.some` chooses a random thing in the
image with this property.

-/

noncomputable def lift (n : ℕ) (r : R) [decidable (r ∈ aux_ideal I n)] : polynomial R :=
if hr : r ∈ aux_ideal I n then (submodule.mem_map.1 hr).some else 0

variables {n : ℕ} {r : R} [decidable (r ∈ aux_ideal I n)]

variable {I}

-- you can use `dif_neg` to prove this lemma.
lemma lift_eq_zero_of_ne (hr : ¬ r ∈ aux_ideal I n) : lift I n r = 0 :=
begin
  sorry
end

-- you need to do a case split for this one. The definition of `lift`
-- used ` (submodule.mem_map.1 hr).some` so this proof will need
-- ` (submodule.mem_map.1 hr).some_spec` somewhere. Note also `dif_pos` :-)
lemma lift_mem :
  (lift I n r) ∈ submodule.restrict_scalars R I ⊓ M R n :=
begin
  sorry
end

-- this is a one-liner
lemma lift_mem_I : lift I n r ∈ I :=
begin
  sorry
end

-- this is a one-liner too (thanks to definitional equality abuse)
lemma lift_nat_degree_le :
  (lift I n r).nat_degree ≤ n :=
begin
  sorry
end

lemma lift_spec (hr : r ∈ aux_ideal I n) :
  lcoeff R n (lift I n r) = r :=
begin
  sorry
end

variable (I)

/-

We finish this (long) section with a couple of trickier proofs. Say
R is Noetherian, and `c ∈ aux_ideal I n`. By `is_noetherian_ring.span_gens`,
`c` is in the span of `hR.gens (aux_ideal I n)`. The claim is that if we `lift`
these generators to `R[X]` then there's an element `y` in the `R`-span of
these lifted generators, whose image in `R` is `c` again. The proof I came
up with of this uses `submodule.span_image`, which says that the span of the
image equals the image of the span. A key intermediate step in my proof is

have h : (hR.gens (aux_ideal I n) : set R) ⊆ (polynomial.lcoeff R n)'' 
    (finset.image (λ (r : R), aux_ideal.lift I n r) (hR.gens (aux_ideal I n))),

-/

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

-/

lemma nat_deg_le_of_mem_span_lift_gens [∀ r, decidable (r ∈ aux_ideal I n)] 
  (hR : is_noetherian_ring R) {p : polynomial R}
  (hp : p ∈ submodule.span R ((λ (r : R), lift I n r) '' (hR.gens (aux_ideal I n)))) :
p.nat_degree ≤ n :=
begin
  sorry,
end

end aux_ideal
