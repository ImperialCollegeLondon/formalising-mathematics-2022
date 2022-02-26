/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import linear_algebra.finite_dimensional

/-!

# Vector spaces

The definition of a vector space `V` over a field `k` is the following:

1) `V` is an abelian group
2) If `r : k` and `v : V` there's an element `r • v : V`
3) Axioms for `•`: `(r + s) • v = r • v + s • v`, `r • (v + w) = r • v = r • w` 
and `1 • v = v`. 

Fields have inverses, but there is no mention of inverses in the axioms of a vector
space. This means that we can make the *definition* of a vector space just under
the assumption that `k` is a `ring`, rather than a `field`, although of course
fewer things will be true (for example, over a general ring it is not true that
every vector space has a basis). However, when `k` is a ring, mathematicians don't
call these things vector spaces; they call them *modules*. So the way we say
"let `V` be a vector space over `k`" in Lean is "let `V` be a module over `k`".

(**TODO** add the vector_space notation back in a locale and PR to mathlib
so that next year's students don't have to suffer this)

-/

-- if we make variable definitions in a section then they will disappear
-- when we close the section
section explanations

-- This says "let `k` be a field and let `V` be a vector space over `k`"
variables (k : Type) [field k] (V : Type) [add_comm_group V] [module k V]

-- This says "let `B` be a basis for `V`, with basis vectors eᵢ for `i : I`"
variables (I : Type) (B : basis I k V)

-- This says "assume `V` is finite-dimensional

variable [finite_dimensional k V]

end explanations

/-

# subspaces of a vector space are a lattice

-/

section lattice

-- Let V be a vector space over a field k
variables (k : Type) [field k] (V : Type) [add_comm_group V] [module k V]

-- let A and B be subspaces
variables (A B : subspace k V)

-- Note that A and B are terms not types.

-- How do we say A ⊆ B?

-- #check A ⊆ B -- doesn't work!

-- We need to use *lattice notation*

#check A ≤ B -- A is a subset of B; it's a Prop

#check A ⊓ B -- intersection of A and B, as a subspace

#check A ⊔ B -- A + B, as a subspace

#check (⊥ : subspace k V) -- the 0-dimensional subspace

#check (⊤ : subspace k V) -- V considered as a subspace of itself; note that
                          -- we can't use V to represent this subspace because
                          -- V is a type, and a subspace of V is a term

-- For elements it's just like sets:

variable (v : V)

#check v ∈ A -- it's a Prop

-- There are a ton of general theorems about lattices such as `A ≤ A ⊔ B`
-- and `A ⊓ B ≤ B` in the library; they apply to all lattices (like the lattice
-- of subsets of a type, the lattice of subgroups of a group etc etc).

end lattice

/-

# The question

A 2019 University of Edinburgh example sheet question: prove that if `V` is a 9-dimensional
vector space and `A, B` are two subspaces of dimension 5, then `A ∩ B` cannot be 
the zero vector space.

-/

-- let k be a field and let V be a k-vector space
variables (k : Type) [field k] (V : Type) [add_comm_group V] [module k V]

-- Let `A` and `B` be subspaces of `V`
variables (A B : subspace k V)

-- If we don't put in a finite-dimensional hypothesis then `dim V` will be a "cardinal",
-- a generalisation of a number which could be infinity. 

variables [finite_dimensional k V]

-- Now we can use `finite_dimensional.finrank k V` which is the dimension of V as a natural number
-- However, if we open the namespace...
open finite_dimensional

-- ...then we can just talk about `finrank` which makes typing easier. Here's the question.

example (hV : finrank k V = 9) (hA : finrank k A = 5) (hB : finrank k B = 5) :
  A ⊓ B ≠ ⊥ :=
begin
  -- see below for the API (i.e. the theorems) you will need
  sorry,
end

/-

## Some API for finite-dimensional vector spaces

`submodule.dim_sup_add_dim_inf_eq A B : finrank k ↥(A ⊔ B) + finrank k ↥(A ⊓ B) = finrank k ↥A + finrank k ↥B`
`submodule.finrank_le A : finrank k ↥A ≤ finrank k V`
`finrank_bot k V : finrank K ↥⊥ = 0`

-/