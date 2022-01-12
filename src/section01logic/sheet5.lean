/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  sorry
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  sorry
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  sorry
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  sorry
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  sorry
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  sorry
end

example : P ↔ (P ∧ true) :=
begin
  sorry
end

example : false ↔ (P ∧ false) :=
begin
  sorry
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  sorry
end

example : ¬ (P ↔ ¬ P) :=
begin
  sorry,
end
