/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Lists

An example of a list of naturals is [1,5,8,1]. More generally, given a
type `X`, a term of type `mylist X` is a finite list of terms of type `X`,
with repeats allowed.

## The definition of a list

The empty list is traditionally called `nil`, and the constructor which
takes a list and adds an element to the beginning is called `cons`,
so `cons 3 [1,5,4] = [3,1,5,4]`. 

We don't set up the `[a,b,c]` notation in this file.

-/

/-- `mylist X` is the type of (finite) lists of elements of `X`. -/
inductive mylist (X : Type) : Type
| nil : mylist -- empty list
| cons (x : X) (l : mylist) : mylist -- "put `(x : X)` at the beginning of `(l : mylist X)`"

namespace mylist

variables (a b c : ℕ)

-- list [a,b,c] of naturals
example : mylist ℕ := cons a (cons b (cons c nil))

variable {X : Type} -- make X implicit

-- joining lists together: [1,5,4] + [2,1] = [1,5,4,2,1]. Defined 
-- by induction on the left list.

/-- Addition of lists. Often called `append` in the literature. -/
def add : mylist X → mylist X → mylist X
| nil l := l
| (cons x m) l := cons x (add m l)

-- Enable `+` notation for addition of lists.
instance : has_add (mylist X) := 
{ add := add }

@[simp] lemma nil_add (a : mylist X) : nil + a = a :=
begin
  sorry
end

@[simp] lemma cons_add (x : X) (m l) : cons x m + l = cons x (m + l) :=
begin
  sorry
end

-- You might want to start this one with `induction a with h t IH`,
@[simp] lemma add_nil (a : mylist X) : a + nil = a :=
begin
  sorry
end

lemma add_assoc (a b c : mylist X) : (a + b) + c = a + (b + c) :=
begin
  sorry
end

-- singleton list
def singleton (x : X) : mylist X := cons x nil

@[simp] lemma singleton_def (x : X) : singleton x = cons x nil :=
begin
  sorry
end

/-- The reverse of a list. -/
def reverse : mylist X → mylist X
| nil := nil
| (cons x m) := (reverse m) + (singleton x)

-- surprisingly difficult question. Geometrically obvious, but so
-- is a + b = b + a for naturals, and this takes some preliminary work.
-- Don't just jump in! Prove things like `reverse_add` and even more basic things first
-- (and consider tagging them with `@[simp]` if you want to train Lean's
-- simplifier to do the work)

theorem reverse_reverse (l : mylist X) : reverse (reverse l) = l :=
begin
  sorry,
end

end mylist
