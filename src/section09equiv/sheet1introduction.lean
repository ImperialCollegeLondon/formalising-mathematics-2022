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

Unfortunately, *using* the above result is *really annoying*. The theorem
says that there *exists* a `g`, but this is a statement in the `Prop`
universe. What we actually want is the inverse itself; this is data, so it
lives in the `Type` universe. Here are the types of everything:

-- this is on the `Prop` side of Lean
`∃ g : Y → X, (∀ y, f(g y)=y) ∧ (∀ x, g(f x) = x) : Prop`

-- these are on the `Type` side of Lean
`g : Y → X`
`Y → X : Type`

In constructive mathematics, or computer science, or whatever you want to
call it, it's impossible to move from the `Prop` universe to the `Type`
universe; we know `g` exists, but we don't have a *formula* for it. 
In mathematics we don't care about this, and we can use what the
computer scientists call "classical axioms" to get `g` from the `∃ g` statement.
For example, `classical.some` is a function which eats a proof of `∃ x : X, <something>`
and returns a term of type `X` which satisfies the `<something>`. It's really inconvenient
having to keep using `classical.some` though. What is done in Lean's maths library
is something different. In Lean, a group isomorphism or a homeomorphism
is defined not to be a bijective function `f : X → Y` with some properties,
but a *pair* of functions `f : X → Y` and `g : Y → X` with some properties
(including the properties of being each other's inverse). In the next
sheet we'll see the `equiv` structure, which packages up the common
data needed in all these definitions; `equiv` is "constructive bijections",
or "bijections with a given inverse".

-/