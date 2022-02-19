import tactic

/-

# Prove that for every positive integer n the number 3(1^5 +2^5 +...+n^5)
# is divisible by 1^3+2^3+...+n^3

This is question 9 in Sierpinski's book

-/

open_locale big_operators

open finset

example (a b : ℤ) : (a : ℚ) = b ↔ a = b := int.cast_inj

lemma sum_cubes (n : ℕ) : ∑ i in range n, (i : ℚ)^3 = (n*(n-1)/2)^2 :=
begin
  induction n with d hd,
  { simp, ring, },
  { rw [finset.sum_range_succ, hd],
    simp,
    ring }
end

lemma sum_fifths (n : ℕ) : ∑ i in range n, (i : ℚ)^5 = (4 * (n * (n-1)/2)^3-(n*(n-1)/2)^2)/3 :=
begin
  induction n with d hd,
  { simp, ring, },
  { rw [finset.sum_range_succ, hd],
    simp,
    ring }
end

example (n : ℕ) : (∑ i in range n, i^3) ∣ (3 * ∑ i in range n, i^5) :=
begin
  rw ← int.coe_nat_dvd,
  use 2 * n * (n-1) - 1,
  rw ← @int.cast_inj ℚ _ _ _ _,
  push_cast,
  rw sum_cubes,
  rw sum_fifths,
  ring,
end

