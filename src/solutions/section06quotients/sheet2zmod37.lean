/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import solutions.section06quotients.sheet1definitions

/-!

## The API for quotients

Right now we have the equivalence relation `R : ℤ → ℤ → Prop` and also
the "setoid" `s : setoid ℤ`. If you did `cases s` you would get
a pair, you'd get `R` and the proof `R_equivalence` that it's an
equivalence relation. But we won't ever need to take `s` apart.

Recall that we've defined `Zmod37` to be `quotient s`. Now here
is the API that we will need. Note that we are not learning
new *tactics* here, we are learning new *theorems from the maths library*.
The same old tactics (`intro`, `apply`, `simp` etc) are useful whether
you're doing algebra, analysis, geometry or whatever. But the theorems
and definitions in the library apply in more specialised domains. 
In this sheet I'll show you the theorems and definitions you'll
need to start working with quotients.

-/

-- `setoid` is a class, so `s` should not just be a definition, we should
-- make it an instance by tagging it with the `instance` attribute

attribute [instance] s

-- This unlocks notation `≈` for the equivalence relation `R`
-- and `⟦x⟧` for the element of `Zmod37` corresponding to the integer `x`.

-- Uncomment the three lines below to see it in action

--def n : ℤ := 23 -- a random integer

--#check ⟦n⟧ -- it's in Zmod37

--#check n ≈ 42 -- it's a true-false statement

-- in fact `⟦a⟧` is just notation for `quotient.mk a`, the
-- function from `X` to `quotient s`. Let's check this.

example (a : ℤ) : ⟦a⟧ = quotient.mk a :=
begin
  refl
end

-- and `≈` is just notation for `R`
-- (this is handy to know; let's give it a name so we can rewrite it)
lemma equiv_def (a b : ℤ) : a ≈ b ↔ R a b :=
begin
  refl
end

-- The theorem that quotient.mk is surjective is called `surjective_quotient_mk`.

example : function.surjective (λ (a : ℤ), ⟦a⟧) :=
begin
  exact surjective_quotient_mk ℤ 
  -- `surjective_quotient_mk` is a theorem in the library
  -- maybe you could have guessed its name?
end

-- The theorem that two integers are related iff their images are equal
-- is called `quotient.eq`.

example (a b : ℤ) : ⟦a⟧ = ⟦b⟧ ↔ a ≈ b :=
begin
  exact quotient.eq -- so `rw quotient.eq` is often useful
end

-- Both implications also have names

example (a b : ℤ) : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
begin
  exact quotient.exact
end

example (a b : ℤ) : a ≈ b → ⟦a⟧ = ⟦b⟧ :=
begin
  exact quotient.sound
end 

/-

## Being "well-defined"

Here is a concept which students sometimes find difficult.

Let's say we want to define a function from `Zmod37` to another type.
For example, when we start putting the additive abelian group structure
on `Zmod37` we will need to define the additive inverse map `neg : Zmod37 → Zmod37`. 
Here's how mathematicians usually explain it.

Step 0) We're defining a function `f : Zmod37 → α` for some type `α`.
Step 1) Choose an element `z` in `Zmod37`. We want to define `f(z)`.
Step 2) Lift `z` completely randomly to an integer `a` in `ℤ` (OK because
the quotient map is surjective). 
Step 3) Now write down a formula for what we want `f(z)` to be,
except that this formula will depend on `a` (for example, in the case of negation we
would define `f(z)=⟦-a⟧` ; note that this makes sense because we already have `neg : ℤ → ℤ`)
Step 4) Now check that "this function is well-defined". This means
the following: say that we had lifted `z` to a different integer `b` in `ℤ`
in step 2. Then we need to check that our recipe for `f(z)` defined using
`a` and our recipe using `b` give the same answer. In the negation case
this would boil down to checking that if `a ≈ b` then `⟦-a⟧ = ⟦-b⟧`. 

See if you can prove the key lemma needed to show that
negation on `Zmod37` is well-defined. 
-/

namespace Zmod

lemma negation_is_well_defined_key_lemma (a b : ℤ) (h : a ≈ b) : ⟦-a⟧ = ⟦-b⟧ :=
begin
  apply quotient.sound,
  cases h with x hx,
  rw equiv_def,
  rw R_def,
  use -x,
  simp [← hx],
end

-- The lemma above is somehow the key ingredient to make those
-- steps above work. Lean has a function called `quotient.lift` which
-- does all the steps at once

def neg : Zmod37 → Zmod37 := quotient.lift (λ a, ⟦-a⟧) (negation_is_well_defined_key_lemma)

/-
The general set-up is as follows: if `Y` is the quotient of `X` by `≈`
then if we want to define a function from `Y` to a type `α` then we
can do it by defining a function `F` from `X` to `α` and then proving
that equivalent elements of `X` get sent to equal elements of `α`. 
Then `quotient.lift` in Lean's library can be fed the function `F`
and the proof, and it will spit out the function `f` from `Y` to `α`
with the property that `f(⟦x⟧)=F(x)`. 

But now here's a question: Let's say we've defined `f` this way.
How do we know that `f(⟦x⟧) = F(x)`? 
Here's what this question boils down to in our case:

-/

example (a : ℤ) : neg ⟦a⟧ = ⟦-a⟧ :=
begin
  refl -- true by definition. That is part of the magic of Lean's quotient types.
end

/-

## A second definition of `neg`

Here is another way of defining `neg` on `Zmod37`. We know that
there's a negation function on `ℤ` sending `n` to `-n`. We want
to "descend" this function to `Zmod37`. The Lean function `quotient.map`
does this for us. The function `quotient.map` eats a function `F : X₁ → X₂`
where `X₁` and `X₂` are types with setoid structures (i.e. equivalence
relations `≈₁` and `≈₂` in the typeclass system) and also eats a proof that
``a ≈₁ b → F a ≈₂ F b`, and spits out the function `f : Y₁ → Y₂` making
the diagram commute (i.e. such that `⟦F(x₁)⟧ = f(⟦x₁⟧)`).

-/
def neg2 : Zmod37 → Zmod37 := quotient.map (λ a, -a) begin
  -- goal looks terrifying! I don't really understand it myself!
  -- But bravely start with `intro a`, and use `dsimp` to get rid of the `lambda`s
  rintros a b ⟨x, hx⟩,
  use -x,
  simp [← hx],
end

-- The diagram commutes by definition
example (a : ℤ) : neg2 ⟦a⟧ = ⟦-a⟧ :=
begin
  refl
end 

-- The two ways of defining negation are definitionally equal as well
example : neg = neg2 :=
begin
  refl
end 

-- We have negation; in the next sheet we'll define addition
-- and then we'll be able to prove `Zmod37` is an additive abelian group.
-- We'll then zip through multiplication and show it's a ring.

end Zmod
