/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import topology.algebra.affine
/-!

# `equiv` -- bijections the easy way

Here's a theorem. Say `f : X → Y` is a function. Then
the following are equivalent:

(1) `f` is a bijection (i.e., injective and surjective)
(2) There exists a function `g : Y → X` which is a
two-sided inverse of `f` (i.e. `f ∘ g` and `g ∘ f` are
both identity functions)

However, trying to prove this in Lean, you run into a perhaps
unexpected hitch. Let's consider following even simpler
theorem. Again say `f : X → Y` is a function. Then I claim
the following are equivalent:

(1) `f` is a surjection;
(2) There exists `g : Y → X` such that `f(g(y))=y` for all `y : Y`.

If you didn't know this already, then pause for a second and write down a proof
on paper before continuing. Consider drawing a picture if this helps.

OK here's the proof. To do (1) implies (2) define `g` thus: if `y : Y` then
by surjectivity of `f` there exists some `x : X` such that `f(x)=y`; define
`g(y)` to be any such `x` and this works. To do (2) implies (1) just note
that if `y : Y` then certainly there exists `x : X` with `f(x)=y` because
we can just take `x=g(y)`.

Did you notice where we used the axiom of choice? Do you know what the axiom of choice is?

To make that function `g : Y → X` in the proof of (1) → (2) we need to make *one object* `g`
which involves making a "random" choice of element `g(y)` from the nonempty set `{x : X | f x = y}`,
for every `y : Y`, all at once. That's exactly what the axiom of choice says that you can do.
In fact the axiom of choice is *equivalent* to the claim that (1) and (2) are equivalent.

-/

example (X Y : Type) (f : X → Y) : function.surjective f ↔ ∃ g : Y → X, ∀ y, f(g y)=y :=
begin
  split,
  { intro hf,
    -- `hf` has type `∀ y, ∃ x, f x = y`.
    choose g hg using hf,
    -- now `g` is a function which, given `y`, chooses such an `x`,
    -- and `hg` says that `f (g y) = y`,
    use g,
    exact hg },
  { rintro ⟨g, hg⟩ y,
    exact ⟨g y, hg y⟩ }
end

-- Now see if you can prove the `bijective` version.
-- The `apply_fun` tactic might be useful. From the docstring:
-- "If we have `h : a = b`, then `apply_fun f at h` will replace this 
-- with `h : f a = f b`."

example (X Y : Type) (f : X → Y) :
  function.bijective f ↔ ∃ g : Y → X, (∀ y, f(g y)=y) ∧ (∀ x, g(f x) = x) :=
begin
  sorry,
end

/-

# The axiom of choice in Lean

Unfortunately, *using* the above result is *really annoying*. For example,
if one wants to talk about 
-/