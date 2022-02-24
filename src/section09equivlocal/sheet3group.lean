/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# group isomorphisms

Here's the challenge. Say `G` and `H` are groups,
and `e : G ≃ H` has the property that the forward map `G → H`
is a group homomorphism. Can you prove that the inverse map `H → G`
is also a group homomorphism?

-/

example (G H : Type) [group G] [group H] (e : G ≃ H)
  (he : ∀ a b : G, e (a * b) = e a * e b) :
  ∀ x y : H, e.symm (x * y) = e.symm x * e.symm y :=
begin
  intros x y,
  apply e.injective,
  rw he,
  simp [e.apply_symm_apply],
end

