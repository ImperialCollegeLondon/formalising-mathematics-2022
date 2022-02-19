import tactic

/-

# Prove that there exists infinitely many positive integers n such that
# 4n² + 1 is divisible both by 5 and 13.

This is the third question in Sierpinski's book "250 elementary problems
in number theory".

maths proof: if n=1 then 4n^2+1 is divisible by 5
so if n=1 mod 5 then 4n^2+1 will be divisible by 5

in fact if n=4 then 4n^2+1 is divisible by both 5 and 13
so if n=4+65*t then this will work
-/

lemma divides_of_cong_four (t : ℕ) : 5 ∣ 4 * (65 * t + 4)^2 + 1 ∧
13 ∣ 4 * (65 * t + 4)^2 + 1 :=
begin
  split,
  { use 3380*t^2 + 416*t + 13,
    ring },
  { use 1300*t^2 + 160*t + 5,
    ring }
end


lemma arb_large_soln : ∀ N : ℕ, ∃ n > N, 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1 :=
begin
  intro N,
  -- need to find t such that 65t+4>N
  use 65 * N + 4,
  split,
  { linarith },
  { apply divides_of_cong_four }  
end

lemma infinite_iff_arb_large (S : set ℕ) : S.infinite ↔ ∀ N, ∃ n > N, n ∈ S :=
begin
  split,
  { intro h,
    have h2 := set.infinite.exists_nat_lt h,
    intro n,
    rcases h2 n with ⟨m, hm, h3⟩,
    use m,
    exact ⟨h3, hm⟩,
  },
  { contrapose!,
    intro h,
    rw set.not_infinite at h,
    let S2 : finset ℕ := set.finite.to_finset h,
    have h2 : ∃ B, ∀n ∈ S2, n ≤ B,
    { use finset.sup S2 id,
      intros,
      apply finset.le_sup H },
    cases h2 with N hN,
    use N,
    have h3 : ∀n : ℕ, n ∈ S ↔ n ∈ S2,
      intro n,
      exact (set.finite.mem_to_finset h).symm,
    intros n hn h4,
    rw h3 at h4,
    specialize hN n h4,
    linarith,
  }
end

example : {n : ℕ | 5 ∣ 4*n^2+1 ∧ 13 ∣ 4*n^2+1}.infinite :=
begin
  rw infinite_iff_arb_large,
  exact arb_large_soln,
end
