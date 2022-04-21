/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.polynomial -- API for (i.e. definitions relating to and lemmas about) polynomials

/-!

# Degree

What is the degree of the zero polynomial? Is it 0, -1 or -∞? One advantage
of -∞ is that things like `deg(f*g)=deg(f)+deg(g)` is always true (at least
if the base is an integral domain) but one big disadvantage is that working
with a type like `with_bot ℕ` (which is the naturals plus a "bottom" element
`⊥` which is less than all naturals) is a pain; it's sometimes much easier to
define `deg(0)` to be the "junk" value `0` and have a degree function
taking values in the naturals.

Lean has both options: there is a function `polynomial.degree` taking
values in `with_bot ℕ` and also a function `polynomial.nat_degree`
taking values in `ℕ`. In this file we use `nat_degree` because for
what we're doing here the benefits outweigh the gains.

## M(R,n), the space of polynomials of degree ≤ n

We are about to embark upon a long proof; a proof that if `R` is a Noetherian
ring (i.e. all its ideals are finitely-generated) then so is `R[X]`. 
One of the players in it will be the free `R`-module of polynomials
of degree at most `n`. We make this definition explicitly. I've
left the proofs of the axioms for you to fill in; you are going to have
to figure out the API for `polynomial.nat_degree` to solve them. Guess
the names of the lemmas you'll need; everything is there somewhere.
If you really can't guess, then browse around the API documentation
for `nat_degree` here:

https://leanprover-community.github.io/mathlib_docs/data/polynomial/degree/definitions.html#polynomial.nat_degree

-/

namespace polynomial

variables (R : Type) [comm_ring R]

/-- `M R n` is the `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
noncomputable def M (n : ℕ) : submodule R (polynomial R) :=
{ carrier := {f : polynomial R | f.nat_degree ≤ n},
  zero_mem' := begin
    sorry
  end,
  add_mem' := begin
    sorry,
  end,
  smul_mem' := begin
    sorry
  end
}

-- think about what `f ∈ M R n` means

lemma mem_M_iff (f : polynomial R) (n : ℕ) : f ∈ M R n ↔ f.nat_degree ≤ n :=
begin
  sorry,
end

/-

## lcoeff

The function `polynomial.coeff` eats a polynomial `f` and a natural `n`, and
returns the coefficient of `X^n` in `f`. However this is just a bare function.
For fixed `n`, the function which eats `f` and returns the coefficient of
`X^n` in `f` is an `R`-linear map, and this `R`-linear map
is called `polynomial.lcoeff R n : polynomial R →ₗ[R] R`. The notation
`→ₗ[R]` means "R-linear map". 

The lemma below, which will be of use for us later, says that a polynomial
of degree ≤ n+1 whose coefficient of X^{n+1} is 0, is actually a polynomial
of degree ≤ n. The proof is not too bad once you know about
`nat_degree_le_iff_coeff_eq_zero`. 

-/

lemma ker_lcoeff (f : polynomial R) (n : ℕ) (hfn : f ∈ M R (n+1)) (hf : lcoeff R (n+1) f = 0) :
  f ∈ M R n :=
begin
  sorry,
end

/-

Finally, this lemma below, saying that the degree of X^n is at most n,
seems to be missing from mathlib. You would have thought that this
was a strange thing to prove because surely the degree of X^n *equals* n,
but in fact there is an edge case where this is false! Can you think of it?

Spoiler alert below.

If R is the zero ring, then R[X] is the zero ring, and X^n=X^2=X=1=0
so clearly X^n can't have degree n. It turns out that 
there's a lemma `nat_degree_of_subsingleton` saying that if `R`
is a so-called "subsingleton" (mathlib's preferred say of saying
that `R` is the zero ring) then every polynomial has `nat_degree` 0.
For `nontrivial` rings (those with `0 ≠ 1`), `nat_degree_X_pow`
works. So your proof could do `cases` on `subsingleton_or_nontrivial R`,
except that because `subsingleton` and `nontrivial` are both typeclasses,
you should use the `casesI` tactic to ensure that the assumptions
are known to the type class inference system.

-/

-- this should be PR'ed to mathlib
lemma nat_degree_X_pow_le (n : ℕ) : (X^n : polynomial R).nat_degree ≤ n :=
begin
  sorry,
end

end polynomial
