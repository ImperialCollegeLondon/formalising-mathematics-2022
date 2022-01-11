/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  sorry
end

example : false → ¬ true :=
begin
  sorry
end

example : ¬ false → true :=
begin
  sorry
end

example : true → ¬ false :=
begin
  sorry
end

example : false → ¬ P :=
begin
  sorry
end

example : P → ¬ P → false :=
begin
  sorry
end

example : P → ¬ (¬ P) :=
begin
  sorry
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  sorry
end

example : ¬ ¬ false → false :=
begin
  sorry
end

example : ¬ ¬ P → P :=
begin
  sorry
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  sorry,
end