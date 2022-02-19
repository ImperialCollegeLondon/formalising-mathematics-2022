import tactic
import data.zmod.basic

/-

# Prove that 19 ∣ 2^(2^(6k+2)) + 3 for k = 0,1,2,... 


This is the fifth question in Sierpinski's book "250 elementary problems
in number theory".

thoughts

if a(k)=2^(2^(6k+2))
then a(k+1)=2^(2^6*2^(6k+2))=a(k)^64

Note that 16^64 is 16 mod 19 according to a brute force calculation
and so all of the a(k) are 16 mod 19 and we're done

-/

lemma sixteen_pow_sixtyfour_mod_nineteen : (16 : zmod 19)^64 = 16 :=
begin
  refl,
end.

example (a b : zmod 19) : (a + b = 0) ↔ a = -b := add_eq_zero_iff_eq_neg
example (k : ℕ) : 19 ∣ 2^(2^(6*k+2))+3 :=
begin
  induction k with d hd,
  { refl },
  have h : 2 ^ 2 ^ (6 * d.succ + 2) = (2 ^ 2 ^ (6 * d + 2)) ^ 64,
  { ring_exp },
  rw [← zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.cast_add, add_eq_zero_iff_eq_neg] at hd ⊢,
  rw h,
  rw nat.cast_pow,
  rw hd,
  convert sixteen_pow_sixtyfour_mod_nineteen,
end





