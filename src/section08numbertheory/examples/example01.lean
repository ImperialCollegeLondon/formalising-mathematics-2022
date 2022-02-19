import tactic

/-

# For which positive integers n does n+1 divide n^2+1?

This is the first question in Sierpinski's book "250 elementary problems
in number theory".

Here's the trick: n+1 divides n^2-1 so if it divides n^2+1
then it divides (n^2+1)-(n^2-1)=2, and n+1>=2 so n+1=2 giving
n=1 as the only solution.

-/

#eval (2 : ℕ) - 3
#eval (2 : ℤ) - 3

--set_option pp.notation false

example (n : ℕ) (hn : 0 < n) : (n + 1) ∣ (n^2 + 1) ↔ n = 1 :=
begin
  split,
  { rintro ⟨c, hc⟩,
    have h1 : (n : ℤ)^2 - 1 = (n + 1) * (n - 1) := by ring,
    zify at hc,
    have h2 : ((n : ℤ) + 1) ∣ 2,
    { use c - (n - 1),
      rw [mul_sub, ← hc, ← h1],
      ring },
    have h3 : (n : ℤ) + 1 ≤ 2 := int.le_of_dvd zero_lt_two h2,
    linarith },
  { rintro rfl,
    norm_num }
end

