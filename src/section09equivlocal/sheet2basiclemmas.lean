/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Basic lemmas

Say `e : X ≃ Y`. We know that `e.to_fun` is one way of getting
access to the underlying function `X → Y`. But Lean gives us
another method. There is a coercion from `X ≃ Y` 
to `X → Y`, sending `e` to `e.to_fun`. The notation for it is `⇑e`
but you don't even have to write it. Look:

-/

variables (X Y : Type) (e : X ≃ Y)

example : X → Y := e.to_fun

example : X → Y := e

-- Because `e.symm : Y ≃ X` we can get the function from `Y` to `X` thus:
-- (the coercion to a function is automatic)

example : Y → X := e.symm

-- This is the notation which is used in mathlib's API for `equiv`.
-- So `mathlib` rewrites our basic facts about these maps 
-- using this notation.

example (x : X) : e.symm (e x) = x :=
begin
  exact equiv.symm_apply_apply e x,
end

-- and the other way
example (y : Y) : e (e.symm y) = y :=
e.apply_symm_apply y -- begin exact end all cancel out; I also use dot notation

-- A useful tactic below is the `apply_fun` tactic. If `h : x = y` is
-- a hypothesis with `x y : A` and if `f : A → B` then `apply_fun f at h`
-- turns `h` into `h : f(x)=f(y)`. 

-- Using `equiv.symm_apply_apply` and `equiv.apply_symm_apply` see if
-- you can prove the below. Note that they're both `simp` lemmas.

-- this is called `e.injective` but can you prove it from first principles?
-- equivalences are injective
example : function.injective (e : X → Y) :=
begin
  intros a b h,
  apply_fun e.symm at h,
  simpa using h,
end

-- this is `equiv.surjective` but can you prove it from first principles?
example : function.surjective (e : X → Y) :=
begin
  sorry,
end

/-


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
  simp,
end

