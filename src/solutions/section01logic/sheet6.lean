/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro hP,
  left,
  exact hP,
end

example : Q → P ∨ Q :=
begin
  intro hQ,
  right,
  exact hQ,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros hPoQ hPR hQR,
  cases hPoQ with hP hQ,
  { apply hPR,
    exact hP },
  { exact hQR hQ }
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro hPoQ,
  cases hPoQ with hP hQ,
  { right, assumption },
  { left, assumption }
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  { rintros ((hP | hQ) | hR),
    { left, exact hP },
    { right, left, exact hQ },
    { right, right, exact hR } },
  { rintros (hP | hQ | hR),
    { left, left, exact hP },
    { left, right, exact hQ },
    { right, exact hR } }
end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  rintro hPR hQS (hP | hQ),
  { left, apply hPR, exact hP },
  { right, exact hQS hQ }
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros hPQ h,
  cases h with hP hR,
  { left, apply hPQ, exact hP },
  { right, exact hR }
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros h1 h2,
  rw [h1, h2],
end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  split,
  { intro h,
    split,
    { intro hP,
      apply h,
      left, 
      exact hP },
    { intro hQ,
      apply h,
      right,
      exact hQ } },
  { rintro ⟨hnP, hnQ⟩ (hP | hQ),
    { apply hnP, exact hP },
    { exact hnQ hQ } }
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  { intro h,
    by_cases hP : P,
    { right,
      intro hQ,
      apply h,
      exact ⟨hP, hQ⟩ },
    { left,
      exact hP } },
  { rintro (hnP | hnQ) ⟨hP, hQ⟩,
    { contradiction },
    { apply hnQ, exact hQ } }
end
