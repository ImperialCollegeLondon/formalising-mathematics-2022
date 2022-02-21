import tactic
import number_theory.divisors -- added to make Bhavik's proof work

/-

# Find all integers x ≠ 3 such that x - 3 divides x^3 - 3

This is the second question in Sierpinski's book "250 elementary problems
in number theory".

my solution: x - 3 divides x^3-27, and hence if it divides x^3-3
then it also divides the difference, which is 24. Conversely,
if x-3 divides 24 then because it divides x^3-27 it also divides x^3-3

-/

example (x : ℤ) : x - 3 ∣ x^3 - 3 ↔ x - 3 ∣ 24 :=
begin
  have h : x-3∣x^3-27,
  { use x^2+3*x+9,
    ring, },
  split,
  { intro h1,
    have h2 := dvd_sub h1 h,
    convert h2,
    ring },
  { intro h1,
    convert dvd_add h h1,
    ring },
end

example (a : ℤ) : a ∣ 24 ↔ a ∈ ({-1,-2,-3,-4,-6,-8,-12,-24,1,2,3,4,6,8,12,24} : set ℤ) :=
begin
  split,
  { intro h,
    have h1 : a ≤ 24 := int.le_of_dvd (by norm_num) h,
    have h2 : -a ∣ 24,
    exact (neg_dvd a 24).mpr h,
    have h3 : -a ≤ 24 := int.le_of_dvd (by norm_num) h2,
    have h4 : -24 ≤ a := by linarith,
--    interval_cases a,
    sorry },
  { intro h,
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h);
    try {norm_num},
    change a = 24 at h,
    rw h },
end

-- Thanks to Bhavik Mehta for showing me how to prove this in Lean
lemma int_dvd_iff (x : ℤ) (n : ℤ) (hn : n ≠ 0) :
  x ∣ n ↔ x.nat_abs ∈ n.nat_abs.divisors :=
by simp [hn]

example (x : ℤ) : x ∣ 24 ↔ x ∈ ({-1,-2,-3,-4,-6,-8,-12,-24,1,2,3,4,6,8,12,24} : set ℤ) :=
begin
  suffices : x ∣ 24 ↔ x.nat_abs ∈ ({1,2,3,4,6,8,12,24} : finset ℕ),
  { simp only [this, int.nat_abs_eq_iff, set.mem_insert_iff, set.mem_singleton_iff,
      finset.mem_insert, finset.mem_singleton],
    norm_cast,
    rw ←eq_iff_iff,
    ac_refl },
  exact int_dvd_iff _ 24 (by norm_num),
end
