/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import solutions.section03groups.sheet1 -- imports our definition of `mygroup`

/-!

# Challenge sheet

This is an optional "puzzle" sheet, which won't teach you any
new Lean concepts but will give you some practice in rewriteology,
and will teach you pretty much all there is to know about the
question "which axioms of a group can I safely drop?" If you're
not into puzzles like this, just move on to sheet 3.

It turns out that two of the axioms in our definition of a group
are not needed; they can be deduced from the others. Let's define
a "weak group" class, where we only have three of the group axioms.
The question is: can you prove that a weak group is a group?
The last def, `to_mygroup`, does this, but you need to fill in the
sorrys first. Note that the simplifier is less use to you now; we've
trained it to solve problems about `mygroup`s but it doesn't
know anything about `myweakgroup`.

-/

-- removing `mul_one` and `mul_inv_self`
class myweakgroup (G : Type)
  extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)

namespace myweakgroup

variables {G : Type} [myweakgroup G] (a b c : G)

/-

One way of doing it: try proving 

`mul_left_cancel : a * b = a * c → b = c`

and then

`mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c`

first.

-/

lemma mul_left_cancel (h : a * b = a * c) : b = c :=
begin
calc 
     b = 1 * b         : by rw one_mul
...    = a⁻¹ * a * b   : by rw inv_mul_self
...    = a⁻¹ * (a * b) : by rw mul_assoc
...    = a⁻¹ * (a * c) : by rw h
...    = a⁻¹ * a * c   : by rw mul_assoc
...    = 1 * c         : by rw inv_mul_self
...    = c             : by rw one_mul
end

lemma mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c :=
begin
  apply mul_left_cancel a⁻¹,
  rw [← mul_assoc, inv_mul_self, one_mul, h],
end

lemma mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw inv_mul_self,
end

lemma mul_inv_self (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

def to_mygroup (G : Type) [myweakgroup G] : mygroup G :=
{ mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  inv_mul_self := inv_mul_self,
  mul_inv_self := mul_inv_self }

end myweakgroup

/-
If you want to take this further: prove that if we make
a new class `my_even_weaker_group` by replacing
`one_mul` by `mul_one` in the definition of `myweakgroup`
then it is no longer true that you can prove `mul_inv_self`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_self` but which really are not groups.
Can you find an example? Try it on paper first. 
-/

-- claim: not a group in general
class my_even_weaker_group (G : Type)
  extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(mul_one : ∀ a : G, a * 1 = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)

instance : my_even_weaker_group bool :=
{ one := tt,
  mul := λ x y, x, -- x * y = x for all x and y
  inv := λ x, tt, -- define x⁻¹ := 1 for all x
  mul_assoc := dec_trivial,
  mul_one := dec_trivial,
  inv_mul_self := dec_trivial }

example : ¬ (∀ g : bool, 1 * g = g) :=
begin
  intro h,
  specialize h ff,
  cases h,
end
