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
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  rw h,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split;
  { intro h,
    rw h}
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros h1 h2,
  rwa h1, -- rwa is rw + assumption
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split;
  { rintro ⟨h1, h2⟩,
    exact ⟨h2, h1⟩ }
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  { intro h,
    cases h with hPaQ hR,
    cases hPaQ with hP hQ,
    split,
    { exact hP },
    { split,
      { exact hQ },
      { exact hR } } },
  { rintro ⟨hP, hQ, hR⟩,
    exact ⟨⟨hP, hQ⟩, hR⟩ }
end

example : P ↔ (P ∧ true) :=
begin
  split,
  { intro hP,
    split,
    { exact hP },
    { triv } },
  { rintro ⟨hP, -⟩,
    exact hP }
end

example : false ↔ (P ∧ false) :=
begin
  split,
  { rintro ⟨⟩ },
  { rintro ⟨-,⟨⟩⟩ }
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intros h1 h2,
  rw h1,
  rw h2,
end

example : ¬ (P ↔ ¬ P) :=
begin
  intro h,
  cases h with h1 h2,
  by_cases hP : P,
  { apply h1; assumption },
  { apply hP,
    apply h2,
    exact hP }
end

-- constructive proof
example : ¬ (P ↔ ¬ P) :=
begin
  intro h,
  have hnP : ¬ P,
  { cases h with h1 h2,
    intro hP,
    apply h1;
    assumption },
  apply hnP,
  rw h,
  exact hnP,
end
