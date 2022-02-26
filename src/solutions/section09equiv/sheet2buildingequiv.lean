/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# `equiv`

Let `X` and `Y` be types. Here's the definition of `X ≃ Y`
(which is notation for `equiv X Y`):

```

structure equiv (X : Type) (Y : Type) :=
(to_fun    : X → Y)
(inv_fun   : Y → X)
(left_inv  : ∀ x : X, inv_fun (to_fun x) = x)
(right_inv : ∀ y : Y, to_fun (inv_fun y) = y)

-- notation
infix ` ≃ `:25 := equiv

```

Here's an example: the identity bijection
between a type and itself:
-/

-- this is called `equiv.refl` in `mathlib`
example (X : Type) : X ≃ X :=
{ to_fun := λ x, x, -- x ↦ x 
  inv_fun := λ y, y,-- y ↦ y
  left_inv := begin
    -- got to check that `∀ x, inv_fun (to_fun x) = x`
    intro x,
    dsimp, -- if you want to check the goal is definitionally `x = x`
    refl,
  end,
  right_inv := begin
    -- goal is definitionally `∀ y, to_fun (inv_fun y) = y`. 
    intro y,
    refl,
  end }

-- now let's see you define `equiv.symm` and `equiv.trans`.
-- Let's start with `equiv.symm`.
-- Note that if `e : X ≃ Y` then `e.to_fun : X → Y`
-- and `e.left_inv` is a proof of `∀ x : X, e.inv_fun (e.to_fun x) = x` etc

example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
{ to_fun := e.inv_fun,
  inv_fun := e.to_fun,
  left_inv := begin exact e.right_inv end,
  right_inv := e.left_inv }


-- can you build `equiv.trans` yourself?
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
{ to_fun := λ x, eYZ.to_fun (eXY.to_fun x),
  inv_fun := λ z, eXY.inv_fun (eYZ.inv_fun z), -- ditto
  left_inv := begin
    intro x,
    dsimp only,
    rw [eYZ.left_inv, eXY.left_inv],
  end,
  right_inv := begin
    intro z,
    dsimp only,
    rw [eXY.right_inv, eYZ.right_inv],
  end }

-- here's the library's version
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
equiv.trans eXY eYZ

-- here it is again using dot notation
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
eXY.trans eYZ

-- See if you can make the following bijection using dot notation
example (A B C X : Type) (eAX : A ≃ X) (eBX : B ≃ X) : A ≃ B :=
eAX.trans eBX.symm

--sorry -- don't use tactic mode, see if you can find a one-liner
-- using `equiv.symm` and `equiv.trans`

-- We already have `equiv.refl ℚ : ℚ ≃ ℚ`, the identity bijection
-- between `ℚ` and itself. See if you can finish making a different one:

example : ℚ ≃ ℚ :=
{ to_fun := λ x, 3 * x + 4,
  inv_fun := λ y, (y-4)/3,
  left_inv := begin
    intro x,
    simp,
    ring,
  end,
  right_inv := begin
    intro y,
    dsimp,
    ring,
  end }


/-

Note that `equiv` is *data* -- `X ≃ Y` doesn't say "`X` bijects with `Y`";
that statement is a true-false statement. A term of type `X ≃ Y`
is *explicit functions* `X → Y` and `Y → X`, together with proofs
that they're inverse bijections.

Clearly there's an equivalence relation going on *somewhere* though:
here it is.  

If `X : Type` then `∃ x : X, true` is just the statement that `X`
is nonempty. It's a proposition. So this works:

-/

-- Two types `X` and `Y` satisfy `R X Y` iff there *exists*
-- a bijection `X ≃ Y`. 
def R (X Y : Type) : Prop := ∃ e : X ≃ Y, true

example : equivalence R :=
begin
  refine ⟨_, _, _⟩,
  { intro X,
    use equiv.refl X },
  { rintros X Y ⟨e, he⟩,
    use e.symm },
  { rintros X Y Z ⟨eXY, -⟩ ⟨eYZ, -⟩,
    use eXY.trans eYZ,
  }
end

-- Remark: the equivalence classes of `R` are called *cardinals*.

