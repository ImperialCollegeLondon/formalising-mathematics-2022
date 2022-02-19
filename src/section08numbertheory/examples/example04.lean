import tactic

/-

# Prove that for positive integer n we have that 
# 169 | 3^{3n+3}-26n-27

This is the fourth question in Sierpinski's book "250 elementary problems
in number theory".

Proof: induction on n; base case n=0 works fine
inductive step 3^{3(n+1)+3}-26(n+1)-27 - 3^{3n+3}-26n-27 is

know 169 | 3^{3n+3}-26n-27
then it divides 27 times this
which is 3^{3(n+1)+3}-26*27*n-27*27
and we want it to divide 3^{3(n+1)+3}-26(n+1)-27

so we're done if it divides the difference, which is
-26n-26-27+26*27n+27*27
=26*26n+26*26 = 13*13*something
-/

example (n : ℕ) (hn : 0 < n) : -- remark; not going to use hn
(169 : ℤ) ∣ 3^(3*n+3)-26*n-27 :=
begin
  clear hn, -- told you
  induction n with d hd, { norm_num },
  rw nat.succ_eq_add_one,
  have h := dvd_mul_of_dvd_right hd ((3 : ℤ)^3),
  rw [mul_sub, mul_sub, ← pow_add] at h,
  rw [mul_add, mul_one, add_comm],
  have h2 : (169 : ℤ) ∣ 169*(4*d+4),
    exact dvd.intro (4 * ↑d + 4) rfl,
  convert dvd_add h h2,
  push_cast,
  ring_exp,
end

