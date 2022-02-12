/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# A word on products

We're going to learn quotients by example, and one
of the examples 
The product of two types `X` and `Y` is `prod X Y`, with notation `X × Y`.
Hover over `×` to find out how to type it.

-/
section product

-- to make a term of a product, use round brackets.
def foo : N2 := (3,4)

-- To extract the first term of a product, use `.1` or `.fst`

example : foo.1 = 3 := 
begin
  -- true by definition.
  refl
end

example : foo.fst = 3 :=
begin
  refl
end

-- similarly use `.2` or `.snd` to get the second term

example : foo.snd = 4 := rfl -- term mode reflexivity of equality

-- The extensionality tactic works for products: a product is determined
-- by the two parts used to make it.
example (X Y : Type) (s t : X × Y) (h1 : s.fst = t.fst) (h2 : s.snd = t.snd) :
  s = t :=
begin
  ext,
  { exact h1 },
  { exact h2 }
end

-- you can uses `cases x` on a product if you want to take it apart into
-- its two pieces
example (A B : Type) (x : A × B) : x = (x.1, x.2) :=
begin
  -- note that this is not yet `refl` -- you have to take `x` apart. 
  cases x with a b,
  -- ⊢ (a, b) = ((a, b).fst, (a, b).snd)
  dsimp only, -- to tidy up: this replaces `(a, b).fst` with `a`.
  -- ⊢ (a, b) = (a, b)
  refl,
end

end product