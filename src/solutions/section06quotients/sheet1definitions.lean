/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Quotients in Lean -- how it works

If `X` is a type and `≈` is an equivalence relation on `X`, then I claim
that there exits a type `Y` and a map `q : X → Y` with the following
two properties:

1) `q` is surjective;
2) `q(x₁) = q(x₂) ↔ x₁ ≈ x₂`.

I want to call `Y` "the quotient of `X` by `≈`" but this name is problematic
for reasons I'll describe a little later on. An important exercise if you
want to understand what's going on here is to figure out what this type
`Y` is before reading the spoiler below.

## My favourite equivalence relation, and a spoiler.

Let me tell you about my favourite equivalence relation. The type `X` is
the collection of red, green, blue and yellow plastic shapes in my office.
I have several hundred of them; they are squares, triangles and pentagons,
they click together, and you can make some pretty cool 3D shapes with them. 
The equivalence relation `≈` on `X` is that two shapes are equivalent if
(and only if) they have the same colour. 

Now here's the spoiler. With notation as above (so back to the general
cases, with `X` a general type and `≈` a general equivalence relation),
we can define `Y` to be the type of equivalence classes for `≈`. Let's
use the notation `⟦x⟧ : Y` to denote the equivalence class of `x : X`. 
The function `q` sends `x` to `⟦x⟧`. You know from earlier on in your
mathematical career that `⟦x₁⟧ = ⟦x₂⟧` if and only if `x₁ ≈ x₂`,
and clearly `q` is surjective because given an arbitrary `y : Y`, it's
an equivalence class and hence by definition equal to `⟦x⟧` for some
element `x` of the class. Hence `Y` and `q` satisfy all the axioms
above.

In the example above, my favourite equivalence relation, there are
four equivalence classes, so `Y` has four elements. One consists of 
about 70 red plastic shapes, one consists of about 70 blue plastic shapes,
one is all the green shapes and one is all the yellow shapes, the
function `q` sends a plastic shape `x` to the element corresponding to its
colour and you can easily check the two axioms above are satisfied.

But here is a second possibility for `Y`. We let `Y` be the set 
`{red, yellow, green, blue}`, and we let `q` be the map sending
a shape to its colour. Again it's easy to check that all the axioms work.

So in fact there is more than one answer to the question "what is `Y`?".
Let's take a closer look at those two answers. Let's call `Y₁` the
first answer (so an element of `Y₁` is a collection of shapes all of which
have the same colour, e.g. "the 70 red shapes"), and let's
call `Y₂` the second answer (so an element of `Y₂` is a colour, e.g. "red").
There are obvious bijections between `Y₁` and `Y₂`, and furthermore
one can check that those bijections "commute with the `q`s" in the sense
that if you do `q₁ : X → Y₁` and then do the bijection, you end up with
the map `q₂ : X → Y₂`. Quotients are unique up to unique isomorphism,
but they are not unique.

This is why I don't like to talk about *the* quotient of `X` by `≈`,
I would rather talk about *a* quotient of `X` by `≈`.

Another example is the ring `ℤ/10ℤ`. When I was at school I imagined
that this quotient ring was `{0,1,2,3,4,5,6,7,8,9}`. At university
I leant that actually the elements were cosets of the ideal `10ℤ` in
the ring `ℤ` and I was foolish enough to believe the lecturer who told
me this. Both of these choices are just *models* for the quotient. 
It doesn't make sense to talk about "the" quotient -- it's nice to know
that models exist, but when we're proving things about quotients
like `ℤ/10ℤ` (e.g. proving that it has a natural ring structure),
the model doesn't matter; all that matters is that there's a "reduce mod 10"
map from `ℤ` to `ℤ/10ℤ` and that the axioms above are satisfied.

## Lean's quotients

Lean's choice of `Y` is called `quotient s`, where `s` is a term which packages
up `X` and `≈` and the proof that `≈` is an equivalence relation all into
one thing. The type of `s` is `setoid X` and to give a term of type `setoid X`
you have to give two pieces of information: a binary relation on `X`,
and a proof that it's an equivalence relation.

## Let's make a quotient

Let's make the quotient `ℤ/37ℤ`. We will do this by starting with the integers,
defining a binary relation `R` on them by `R a b` is true iff `a` and `b`
are congruent mod `37`, proving it's an equivalence relation, making
the corresponding term `s : setoid ℤ` and then defining `Zmod37` to be the
quotient.

-/

/-- The binary relation `R a b` is defined to be the statement that `a - b`
is a multiple of 37. -/
def R (a b : ℤ) : Prop :=
∃ z : ℤ, a - b = 37 * z

lemma R_def (a b : ℤ) : R a b ↔ ∃ z : ℤ, a - b = 37 * z :=
begin
  refl,
end


lemma R_reflexive : reflexive R :=
begin
  unfold reflexive, -- if you like
  sorry
end

lemma R_symmetric : symmetric R :=
begin
  sorry
end

lemma R_transitive : transitive R :=
begin
  sorry
end

lemma R_equivalence : equivalence R :=
begin
  sorry,
end

-- The "setoid" -- everything we've defined and proved so far,
-- all bundled up into one term
def s : setoid ℤ :=
{ r := R,
  iseqv := R_equivalence }

-- Let's not make a definition, let's just make notation
notation `Zmod37` := quotient s 

-- Then `Zmod37` and `quotient s` are syntactically equal 

/-

In the next sheet we'll start to learn about the
API for `quotient`. We'll learn the name of the
map from `ℤ` to `Zmod37`, we'll set up the notation
`≈` and `⟦x⟧`, and we'll prove the two axioms, as well
as discussing another fundamental property of quotients.

-/