/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.nat.modeq -- `a ≡ b [MOD n]`
import data.int.modeq 

example : 2 ≡ 10 [MOD 4] :=
begin
  rw nat.modeq_iff_dvd,
  norm_num,
end

example : ¬ (∃ x y : ℕ, 2*x^4+4*x*y^2+6=8*y^3+10*x+13) :=
begin
  rintro ⟨x, y, h⟩,
  have h1 : (2 : ℤ) ∣ (2 * x ^ 4 + 4 * x * y ^ 2 + 6) - (8 * y ^ 3 + 10 * x + 12),
    use x^4+2*x*y^2+3 - (4*y^3+5*x+6),
    ring,
  zify at h,
  rw h at h1,
  ring_nf at h1,
  revert h1,
  norm_num,
end

example : ¬ (∃ x y : ℕ, 2*x^4+4*x*y^2+6=8*y^3+10*x+13) :=
begin
  rintro ⟨x, y, h⟩,
  zify at h,
  have h2 : (0 : ℤ) ≡ 1 [ZMOD 4],
  calc (0 : ℤ) ≡ 2 * x ^ 4 + 4 * x * y ^ 2 + 6 [ZMOD 4] : by { sorry }
...      ≡ 8 * y ^ 3 + 10 * x + 13 [ZMOD 4] : by { rw h }
...      ≡ 1 [ZMOD 4] : sorry,
  revert h2,
  rw int.modeq_iff_dvd,
  norm_num,
end

example (a b c d n : ℤ) (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
  a + c ≡ b + d [ZMOD n] :=
begin
  exact int.modeq.add h1 h2
end


example (x : ℤ) : 4 ∣ x^2 ∨ 4 ∣ x^2-1 :=
begin
  
end

example : ¬ ∃ (x y : ℤ), x^2+y^2= 40000000000000000000003 :=
begin
  rintro ⟨x, y, h⟩,
  have h1 : (4 : ℤ) ∣ x^2+y^2-3,
    rw h,
    norm_num,
  
end



