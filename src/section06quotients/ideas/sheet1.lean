/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# The integers mod 37

A demonstration of how to use equivalence relations and equivalence classes in Lean.

We define the "congruent mod 37" relation on integers, prove it is an equivalence
relation, define Zmod37 to be the equivalence classes, and put a ring structure on
the quotient.

-/

-- Definition of the equivalence relation
definition R (a b : ℤ) : Prop :=
∃ (k : ℤ), k * 37 = b - a

-- Now let's make an API for `R`.

namespace R

theorem defn (a b : ℤ) : R a b ↔ ∃ k, k * 37 = b - a :=
begin
  refl
end

theorem refl : reflexive R :=
begin
  -- if you're not sure what the goal is,
  -- either work it out, or peek with `unfold reflexive`.
  sorry 
end

theorem symm : symmetric R :=
begin
  sorry,
end

theorem trans : transitive R :=
begin
  sorry,
end

-- so we've now seen a general technique for proving a ≈ b -- use (the k that works)

theorem equiv : equivalence R :=
⟨R.refl, R.symm, R.trans⟩

-- Now let's put an equivalence relation on ℤ
instance setoid : setoid ℤ :=
{ r := R,
  iseqv := R.equiv }

-- Now we can make the quotient.
definition Zmod37 := quotient R.setoid

-- now a little bit of basic interface

namespace Zmod37

-- The name for the quotient map ℤ → Zmod37 is `quotient.mk`
-- and the notation for it is a ↦ ⟦a⟧ (or, as the computer scientists
-- would say, λ a, ⟦a⟧ )

example (a : ℤ) : ⟦a⟧ = quotient.mk a :=
begin
  refl
end

-- **TODO** Do I need this
-- Let's now set up a coercion.
--definition coe_int_Zmod37 : has_coe ℤ (Zmod37) := ⟨reduce_mod37⟩

-- **TODO** Do I need this
-- Let's tell Lean that given an integer, it can consider it as
-- an integer mod 37 automatically.
--local attribute [instance] coe_int_Zmod37

-- **TODO** Do we need this
-- Add basic facts about 0 and 1 to the set of simp facts
--@[simp] theorem of_int_zero : (0 : (Zmod37))  = reduce_mod37 0 := rfl
--@[simp] theorem of_int_one : (1 : (Zmod37))  = reduce_mod37 1 := rfl

/-

## Making Zmod37 into an additive group

### Part 1: defining the *data*

First we need to define 0, addition, and negation. We will do them
in order of complexity; that is, zero, then negation, then addition.

-/

instance : has_zero (Zmod37) :=
{ zero := ⟦0⟧ }

-- `has_zero` is a notation typeclass. They're the easiest kind of
-- typeclass. 

-- uncomment to check it works now
-- #check (0 : Zmod37) 


-- now back to the maths

-- here's a useful lemma -- it's needed to prove addition is well-defined on the quotient.
-- Note the use of quotient.sound to get from Zmod37 back to Z

lemma congr_add (a₁ a₂ b₁ b₂ : ℤ) : a₁ ≈ b₁ → a₂ ≈ b₂ → ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧ :=
begin
  intros H1 H2,
  cases H1 with m Hm, -- Hm : m * 37 = b₁ - a₁
  cases H2 with n Hn, -- Hn : n * 37 = b₂ - a₂
  -- goal is ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧
  apply quotient.sound,
  -- goal now a₁ + a₂ ≈ b₁ + b₂, and we know how to do these.
  use (m + n),
  rw [add_mul, Hm, Hn], ring
end

-- That lemma above is *exactly* what we need to make sure addition is
-- well-defined on Zmod37, so let's do this now, using quotient.lift

-- note: stuff like "add" is used everywhere so it's best to protect.
protected definition add : Zmod37 → Zmod37 → Zmod37 :=
quotient.lift₂ (λ a b : ℤ, ⟦a + b⟧) (begin
  show ∀ (a₁ a₂ b₁ b₂ : ℤ), a₁ ≈ b₁ → a₂ ≈ b₂ → ⟦a₁ + a₂⟧ = ⟦b₁ + b₂⟧,
  -- that's what quotient.lift₂ reduces us to doing. But we did it already!
  exact congr_add,
end)

-- Now here's the lemma we need for the definition of neg

-- I spelt out the proof for add, here's a quick term proof for neg.

lemma congr_neg (a b : ℤ) : a ≈ b → ⟦-a⟧ = ⟦-b⟧ :=
λ ⟨m, Hm⟩, quotient.sound ⟨-m, by simp [Hm]⟩

#check quotient.map₂

protected def neg : Zmod37 → Zmod37 := quotient.lift (λ a : ℤ, ⟦-a⟧) congr_neg

-- For multiplication I won't even bother proving the lemma, I'll just let ring do it

protected def mul : Zmod37 → Zmod37 → Zmod37 :=
quotient.lift₂ (λ a b : ℤ, ⟦a * b⟧) (λ a₁ a₂ b₁ b₂ ⟨m₁, H₁⟩ ⟨m₂, H₂⟩,
  quotient.sound ⟨b₁ * m₂ + a₂ * m₁, by rw [add_mul, mul_assoc, mul_assoc, H₁, H₂]; ring⟩)

-- this adds notation to the quotient

instance : has_add (Zmod37) := ⟨Zmod37.add⟩
instance : has_neg (Zmod37) := ⟨Zmod37.neg⟩
instance : has_mul (Zmod37) := ⟨Zmod37.mul⟩

-- these are now very cool proofs:
@[simp] lemma coe_add {a b : ℤ} : (↑(a + b) : Zmod37) = ↑a + ↑b := rfl
@[simp] lemma coe_neg {a : ℤ} : (↑(-a) : Zmod37) = -↑a := rfl
@[simp] lemma coe_mul {a b : ℤ} : (↑(a * b) : Zmod37) = ↑a * ↑b := rfl

-- Note that the proof of these results is `rfl`. If we had defined addition
-- on the quotient in the standard way that mathematicians do,
-- by choosing representatives and then adding them,
-- then the proof would not be rfl. This is the power of quotient.lift.

-- Now here's how to use quotient.induction_on and quotient.sound

instance : add_comm_group (Zmod37)  :=
{ add_comm_group .
  zero         := 0, -- because we already defined has_zero
  add          := (+), -- could also have written has_add.add or Zmod37.add
  neg          := has_neg.neg,
  zero_add     :=
    λ abar, quotient.induction_on abar (begin
      -- goal is ∀ (a : ℤ), 0 + ⟦a⟧ = ⟦a⟧ -- that's what quotient.induction_on does for us
      intro a,
      apply quotient.sound, -- works because 0 + ⟦a⟧ is by definition ⟦0⟧ + ⟦a⟧ which
                            -- is by definition ⟦0 + a⟧
      -- goal is now 0 + a ≈ a
      -- here's the way we used to do it.
      use (0 : ℤ),
      simp,
      -- but there are tricks now, which I'll show you with add_zero and add_assoc.
    end),
  add_assoc    := λ abar bbar cbar,quotient.induction_on₃ abar bbar cbar (λ a b c,
    begin
      -- goal now ⟦a⟧ + ⟦b⟧ + ⟦c⟧ = ⟦a⟧ + (⟦b⟧ + ⟦c⟧)
      apply quotient.sound,
      -- goal now a + b + c ≈ a + (b + c)
      rw add_assoc, -- done :-) because after a rw a goal is closed if it's of the form x ≈ x,
                    -- as ≈ is known by Lean to be reflexive.
    end),
  add_zero     := -- I will intrroduce some more sneaky stuff now now
                  -- add_zero for Zmod37 follows from add_zero on Z.
                  -- Note use of $ instead of the brackets
    λ abar, quotient.induction_on abar $ λ a, quotient.sound $ by rw add_zero,
                  -- that's it! Term mode proof.
  add_left_neg := -- super-slow method not even using quotient.induction_on
    begin
      intro abar,
      cases (quot.exists_rep abar) with a Ha,
      rw [←Ha],
      apply quot.sound,
      use (0 : ℤ),
      simp,
    end,
  -- but really all proofs should just look something like this
  add_comm     := λ abar bbar, quotient.induction_on₂ abar bbar $
    λ _ _,quotient.sound $ by rw add_comm,
  -- the noise at the beginning is just the machine; all the work is done by the rewrite
}

-- Now let's just nail this using all the tricks in the book. All ring axioms on the quotient
-- follow from the corresponding axioms for Z.
instance : comm_ring (Zmod37) :=
{
  mul := Zmod37.mul, -- could have written (*)
  -- Now look how the proof of mul_assoc is just the same structure as add_comm above
  -- but with three variables not two
  mul_assoc := λ a b c, quotient.induction_on₃ a b c $ λ _ _ _, quotient.sound $
    by rw mul_assoc,
  one := 1,
  one_mul := λ a, quotient.induction_on a $ λ _, quotient.sound $ by rw one_mul,
  mul_one := λ a, quotient.induction_on a $ λ _, quotient.sound $ by rw mul_one,
  left_distrib := λ a b c, quotient.induction_on₃ a b c $ λ _ _ _, quotient.sound $
    by rw left_distrib,
  right_distrib := λ a b c, quotient.induction_on₃ a b c $ λ _ _ _, quotient.sound $
    by rw right_distrib,
  mul_comm := λ a b, quotient.induction_on₂ a b $ λ _ _, quotient.sound $ by rw mul_comm,
  ..Zmod37.add_comm_group
}

end Zmod37
