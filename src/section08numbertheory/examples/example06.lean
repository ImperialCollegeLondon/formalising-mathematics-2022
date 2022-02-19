import tactic
import data.zmod.basic
import field_theory.finite.basic
/-

# Prove the theorem, due to Kraichik, asserting that 13|2^70+3^70

This is the sixth question in Sierpinski's book "250 elementary problems
in number theory".

-/

example : 13 ∣ 2^70 + 3^70 :=
begin
  use 192550423461109399456637645953021,
  norm_num,
end


/-

thoughts

2,4,8,3,6,12=-1,-2,-4,-8,-3,-6,1 2^12=1 mod 13

3,9,1
-/

example : 13 ∣ 2^70 + 3^70 :=
begin
  rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd,
  push_cast,
  change (2 : zmod 13) ^ 70 + (3 : zmod 13) ^ 70 = 0,
  have h0 : nat.prime 13 := by norm_num,
  haveI : fact (nat.prime 13) := ⟨h0⟩,
  have h1 : (2 : zmod 13)^12 = 1,
  { apply zmod.pow_card_sub_one_eq_one,
    intro h2,
    have h3 : ((2 : ℕ) : zmod 13) = 0,
      assumption_mod_cast,
    rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h3,
    revert h3,
    norm_num,
  },
  have h2 : (3 : zmod 13)^3 = 1,
    refl,
  conv_lhs begin
    congr,
    rw (show 70 = 12 * 5 + 10, by norm_num),
    skip,
    rw (show 70 = 3 * 23 + 1, by norm_num),
  end,
  rw [pow_add, pow_add, pow_mul, pow_mul, h1, h2],
  simp,
  refl,
end
