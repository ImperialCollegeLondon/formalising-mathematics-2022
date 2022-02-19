/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import topology.continuous_function.compact -- continuous functions, compact sets

/-!

# Topology : continuous image of compact is compact

Useful API for this proof:

* `continuous.is_open_preimage` : preimage of open under continuous map is open


-/

-- let X & Y be topological spaces
variables (X Y : Type) [topological_space X] [topological_space Y]

-- let S be a subset of X
variable (S : set X)

-- Let `f : X → Y` be a function
variables (f : X → Y) 

-- If f is continuous and S is compact, then the image f(S) is also compact.
example (hf : continuous f) (hS : is_compact S) : is_compact (f '' S) :=
begin
  -- use defn of compact
  rw is_compact_iff_finite_subcover at hS ⊢,
  -- cover f(S) with opens U_i
  intros I U hUopen hUfS,
  -- f⁻¹(U_i) are an open cover of S
  specialize hS (λ i, f ⁻¹' U i) _ _,
  { intro j,
    exact continuous.is_open_preimage hf (U j) (hUopen j) }, -- open
  { finish }, -- cover
  -- so have a finite subcover f⁻¹(U_1), f⁻¹(U_2), ... f⁻¹(U_n)
  -- and Lean can take it from there
  finish,
end
