/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import solutions.section14polynomials.sheet01degree

/-!

# Noetherian rings

`is_noetherian_ring R` is the predicate that `R` is Noetherian,
i.e., that all ideals of `R` are finitely generated. The theorem
saying that a ring is Noetherian iff all ideals are finitely
generated is called `is_noetherian_ring_iff_ideal_fg R`. 

Let me explain the definition of `gens` below. 

`is_noetherian_ring_iff_ideal_fg R` is the statement that R is 
  Noetherian ↔ all ideals are finitely generated. An `↔` statement
  is made in Lean by giving two things; the `→` implication and the `←`
  implication.

`(is_noetherian_ring_iff_ideal_fg R).1` is the first implication,
namely that if `R` is Noetherian then all ideals are finitely generated.

If `hR : is_noetherian_ring R` then
`(is_noetherian_ring_iff_ideal_fg R).1 hR` is thus the statement
that for all ideals of `R`, they're finitely generated. So it's
a function which eats an ideal of `R` and returns a proof that
it's finitely generated.

If furthermore `J` is an ideal of `R` then
`(is_noetherian_ring_iff_ideal_fg R).1 hR J` is thus the proof that `J`
is finitely-generated. In other words, it's a proof there exists
a finite set `S : finset R` of elements of `R` such that `S` generates `J`
as an ideal.

`exists.some` is the function which takes a proof
that there exists something with a property, and spits out
a something. It moves from the `Prop` universe to the `Type` universe
and is hence noncomputable. The proof that the something satisfies
the property is `exists.some_spec`.

With that in mind, I present `is_noetherian_ring.gens`, a function
which eats an ideal of a Noetherian ring and produces a finite
generating set.

-/

variables {R : Type} [comm_ring R] (I : ideal (polynomial R))

open polynomial

-- this definition and these lemmas should perhaps be in mathlib?
namespace is_noetherian_ring

/-- If `hR : is_noetherian_ring R` and `J : ideal R` then `hR.gens J` is a finite generating set for `J`,
  expressed as a term of type `finset R`. See `hR.span_gens J` for a proof that it spans. -/
noncomputable def gens (hR : is_noetherian_ring R) (J : ideal R) : finset R :=
((is_noetherian_ring_iff_ideal_fg R).1 hR J).some

/-

The `gens` function spits out a `finset`, which is the type of finite subsets
of `R`. There's a coercion to `set R` of course. 

The proof that the generating set does actually span is the same as the
definition, except that you change `some` to `some_spec`.

-/

lemma span_gens (hR : is_noetherian_ring R) (J : ideal R) : ideal.span (hR.gens J : set R) = J :=
((is_noetherian_ring_iff_ideal_fg R).1 hR J).some_spec

/-

See if you can prove the useful lemma that the generators of `J` are a subset
of `J`. The lemma you need from the library is called `ideal.subset_span`.
-/

lemma gens_subset (hR : is_noetherian_ring R) (J : ideal R) :
  (hR.gens J : set R) ⊆ J :=
begin
  have h := hR.span_gens J,
  nth_rewrite 1 ← h,
  exact ideal.subset_span,
end

end is_noetherian_ring
