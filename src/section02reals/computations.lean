import tactic -- imports all the tactics
import data.real.sqrt -- don't need this

open real

example (h : ∃ x : ℝ, x * x = 2) : ∃ y : ℝ, y * y = 8 :=
begin
  cases h with x hx,
  use 2 * x,
  -- can't use `ring` directly on the goal
  -- so let's create the hypothesis which we want to `rw` to make progress.
  have h : 2 * x * (2 * x) = 4 * (x * x),
  { ring }, -- I put the proof in `{}` because we have two goals
  rw h, -- now we can use `hx`
  rw hx,
  norm_num,
end

-- too hard -- need API
example : 1.41421356 < sqrt 2 :=
begin
  rw mul_self_lt_mul_self_iff,
  rw mul_self_sqrt,
  all_goals { try { norm_num } },
  apply sqrt_nonneg,
end

example :  sqrt 2 < 1.41421357 :=
begin
  rw mul_self_lt_mul_self_iff,
  rw mul_self_sqrt,
  all_goals {try {norm_num}},
  exact (2 : ℝ).sqrt_nonneg,
end

example (x y : ℝ) (h : x^2 = y^2) : x^4 = y^4 :=
begin
  have h2 : x^4=(x^2)^2, -- introduce a new goal
  { ring }, -- proves ``h2``; note that the `{...}` brackets are good practice 
            -- when there is more than one goal
  rw h2, -- goal now ``⊢ (x ^ 2) ^ 2 = y ^ 4``...
  rw h, -- ...so ``rw h`` now works, giving us ``⊢ (y ^ 2) ^ 2 = y ^ 4``
  ring,
end
