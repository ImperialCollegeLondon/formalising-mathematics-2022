/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro hPaQ,
  cases hPaQ with hP hQ,
  exact hP,
end

example : P ∧ Q → Q :=
begin
  rintro ⟨hP, hQ⟩,
  assumption,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  rintro hPQR ⟨hP, hQ⟩,
  apply hPQR;
  assumption,
end

example : P → Q → P ∧ Q :=
begin
  intro hP,
  intro hQ,
  split,
  { exact hP },
  { exact hQ }
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩,
end

example : P → P ∧ true :=
begin
  intro hP,
  split,
  { exact hP },
  { triv },
end

example : false → P ∧ false :=
begin
  intro h,
  exfalso,
  exact h,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  rintro ⟨hP, hQ⟩ ⟨-, hR⟩,
  exact ⟨hP, hR⟩,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros h hP hQ,
  apply h,
  split; assumption,
end



